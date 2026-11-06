(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import MmapSim.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition bottomup_floor : Z := 0x2AAAAAAAB000.
Lemma bottomup_floor_val : bottomup_floor = 46912496119808.
Proof. reflexivity. Qed.

Fixpoint zsum {A} (f : A -> Z) (l : list A) : Z :=
  match l with [] => 0 | x :: l' => f x + zsum f l' end.

Lemma zsum_app {A} (f : A -> Z) l1 l2 : zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. induction l1; cbn; lia. Qed.

Lemma zsum_mono {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
Proof. induction l as [|x l IH]; intros H; cbn; [lia|]. pose proof (H x (or_introl eq_refl)). assert (zsum f l <= zsum g l) by (apply IH; intros; apply H; right; auto). lia. Qed.

Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

Lemma zlen_filter_le {A} (p : A -> bool) l : zlen (List.filter p l) <= zlen l.
Proof. unfold zlen. induction l as [|x l IH]; cbn; [lia|]. destruct (p x); cbn; lia. Qed.

Lemma zlen_filter_existsb {A B} (t : B -> A -> bool) (es : list B) (l : list A) :
  zlen (List.filter (fun k => existsb (fun e => t e k) es) l) <= zsum (fun e => zlen (List.filter (t e) l)) es.
Proof.
  induction es as [|e es IH]; cbn.
  - unfold zlen. induction l; cbn; [lia| exact IHl].
  - assert (G : forall l', zlen (List.filter (fun k => t e k || existsb (fun e0 => t e0 k) es) l')
                          <= zlen (List.filter (t e) l') + zlen (List.filter (fun k => existsb (fun e0 => t e0 k) es) l')).
    { intros l'. unfold zlen. induction l' as [|x l' IHl]; cbn; [lia|]. destruct (t e x), (existsb _ es); cbn; lia. }
    specialize (G l). lia.
Qed.

Lemma zlen_filter_range (p : Z -> bool) lo hi : forall (len : nat) a,
  (forall k, p k = true -> lo <= k <= hi) -> lo <= hi + 1 ->
  zlen (List.filter p (map (fun i => a + Z.of_nat i) (seq 0 len))) <= Z.max 0 (Z.min (a + Z.of_nat len) (hi + 1) - Z.max a lo).
Proof.
  induction len as [|len IH]; intros a Hp Hlh.
  - unfold zlen. cbn. lia.
  - cbn [seq map]. rewrite <- seq_shift, map_map. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    assert (E : map (fun x => a + Z.of_nat (S x)) (seq 0 len) = map (fun i => (a + 1) + Z.of_nat i) (seq 0 len)).
    { apply map_ext. intros; lia. }
    rewrite E. specialize (IH (a + 1) Hp Hlh). cbn [List.filter].
    destruct (p a) eqn:P0.
    + pose proof (Hp _ P0). unfold zlen in *. cbn [length]. lia.
    + unfold zlen in *. lia.
Qed.

Lemma zlen_filter_none {A} (p : A -> bool) l : (forall x, p x = false) -> zlen (List.filter p l) = 0.
Proof. intros H. unfold zlen. induction l as [|x l IH]; cbn; [lia|]. rewrite H. exact IH. Qed.

Lemma filter_short_has_miss {A} (p : A -> bool) l : zlen (List.filter p l) < zlen l -> exists x, In x l /\ p x = false.
Proof.
  unfold zlen. induction l as [|x l IH]; cbn; [lia|]. destruct (p x) eqn:P; cbn; intros H.
  - destruct IH as (y & Hy & Py); [lia|]. exists y. auto.
  - exists x. auto.
Qed.

Section SLOTS.
Variables (F n' : Z).
Hypothesis Hn : 0 < n'.

Definition touches (e : Z * Z) (k : Z) : bool :=
  (fst e <? F + (k + 1) * n') && (F + k * n' <? fst e + snd e).

Lemma div_le_of_lt_mul a k : a < (k + 1) * n' -> a / n' <= k.
Proof. intros H. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. Qed.
Lemma le_div_of_mul_le a k : k * n' <= a -> k <= a / n'.
Proof. intros H. apply Z.div_le_lower_bound; lia. Qed.

Lemma touches_range e k : touches e k = true -> (fst e - F) / n' <= k <= (fst e + snd e - 1 - F) / n'.
Proof.
  unfold touches. intros H. apply andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. split.
  - apply div_le_of_lt_mul. lia.
  - apply le_div_of_mul_le. lia.
Qed.

Lemma touch_count_le e (K : nat) :
  0 <= snd e -> zlen (List.filter (touches e) (map (fun i => 0 + Z.of_nat i) (seq 0 K))) <= snd e / n' + 2.
Proof.
  intros He.
  set (lo := (fst e - F) / n'). set (hi := (fst e + snd e - 1 - F) / n').
  assert (Hhl : hi - lo <= snd e / n' + 1).
  { subst lo hi.
    assert ((fst e + snd e - 1 - F) / n' - (fst e - F) / n' <= ((fst e + snd e - 1 - F) - (fst e - F)) / n' + 1).
    { pose proof (Z.div_mod (fst e + snd e - 1 - F) n' ltac:(lia)). pose proof (Z.div_mod (fst e - F) n' ltac:(lia)).
      pose proof (Z.mod_pos_bound (fst e + snd e - 1 - F) n' Hn). pose proof (Z.mod_pos_bound (fst e - F) n' Hn).
      set (q1 := (fst e + snd e - 1 - F) / n') in *. set (q2 := (fst e - F) / n') in *.
      assert (q1 - q2 - 1 <= (fst e + snd e - 1 - F - (fst e - F)) / n'); [| lia].
      apply Z.div_le_lower_bound; [lia|]. nia. }
    replace (fst e + snd e - 1 - F - (fst e - F)) with (snd e - 1) in H by lia.
    assert ((snd e - 1) / n' <= snd e / n') by (apply Z.div_le_mono; lia). lia. }
  destruct (Z_lt_le_dec hi lo) as [D|D].
  -
    rewrite zlen_filter_none; [pose proof (Z.div_pos (snd e) n' He ltac:(lia)); lia|].
    intros k. destruct (touches e k) eqn:T; [| reflexivity]. pose proof (touches_range e k T). subst lo hi. lia.
  - assert (Z0 : zlen (List.filter (touches e) (map (fun i => 0 + Z.of_nat i) (seq 0 K))) <= Z.max 0 (Z.min (0 + Z.of_nat K) (hi + 1) - Z.max 0 lo)).
    { apply zlen_filter_range; [| lia]. intros k Hk. pose proof (touches_range e k Hk). subst lo hi. lia. }
    pose proof (Z.div_pos (snd e) n' He ltac:(lia)). lia.
Qed.

Theorem free_slot_exists (es : list (Z * Z)) (K : nat) :
  (forall e, In e es -> 0 <= snd e) ->
  zsum (fun e => snd e / n' + 2) es < Z.of_nat K ->
  exists k, 0 <= k < Z.of_nat K /\ forall e, In e es -> touches e k = false.
Proof.
  intros Hes HK.
  set (l := map (fun i => 0 + Z.of_nat i) (seq 0 K)).
  assert (HL : zlen l = Z.of_nat K) by (unfold zlen, l; rewrite map_length, seq_length; reflexivity).
  destruct (filter_short_has_miss (fun k => existsb (fun e => touches e k) es) l) as (k & Hk & Pk).
  { eapply Z.le_lt_trans; [apply zlen_filter_existsb|]. rewrite HL.
    eapply Z.le_lt_trans; [| exact HK]. apply zsum_mono. intros e He. apply touch_count_le. apply Hes. exact He. }
  exists k. split.
  - unfold l in Hk. apply in_map_iff in Hk as (i & <- & Hi). apply in_seq in Hi. lia.
  - intros e He. destruct (touches e k) eqn:T; [| reflexivity]. exfalso.
    assert (X : existsb (fun e0 => touches e0 k) es = true) by (apply existsb_exists; exists e; auto). rewrite X in Pk. discriminate Pk.
Qed.
End SLOTS.

Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma zsum_div_le {A} (f : A -> Z) n l : 0 < n -> (forall x, In x l -> 0 <= f x) -> zsum (fun x => f x / n) l <= zsum f l / n.
Proof.
  intros Hn. induction l as [|x l IH]; intros Hf; cbn; [rewrite Z.div_0_l by lia; lia|].
  assert (0 <= f x) by (apply Hf; left; reflexivity).
  assert (IH' : zsum (fun x => f x / n) l <= zsum f l / n) by (apply IH; intros; apply Hf; right; assumption).
  assert (f x / n + zsum f l / n <= (f x + zsum f l) / n); [| lia].
  apply Z.div_le_lower_bound; [lia|].
  rewrite Z.mul_add_distr_l.
  pose proof (Z.mul_div_le (f x) n Hn). pose proof (Z.mul_div_le (zsum f l) n Hn). lia.
Qed.

Lemma zsum_map {A B} (g : A -> B) (f : B -> Z) l : zsum f (map g l) = zsum (fun x => f (g x)) l.
Proof. induction l; cbn; congruence. Qed.

Lemma zsum_add_const {A} (f : A -> Z) c l : zsum (fun x => f x + c) l = zsum f l + c * zlen l.
Proof. unfold zlen. induction l; cbn; [lia|]. rewrite IHl. cbn [length]. lia. Qed.

Lemma w_range (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w). unfold bv_modulus in *. lia. Qed.

Lemma unsigned_lit' z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Theorem gap_exists (ents : list (word * word)) (F T nZ E B : Z) :
  0 < F -> F mod page_size = 0 -> T < 2 ^ 64 ->
  0 < nZ -> nZ mod page_size = 0 ->
  zlen ents <= E -> zsum (fun e => bv_unsigned (snd e)) ents <= B -> 0 <= B ->
  B / nZ + 2 * E < (T - F) / nZ ->
  exists a, F <= a /\ a + nZ <= T /\ a mod page_size = 0 /\ 0 < a /\
            region_free ents (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros HF0 HFal HT Hn Hal HE HB HB0 HK.
  assert (HKpos : 0 <= (T - F) / nZ).
  { destruct (Z_le_gt_dec F T) as [D|D]; [apply Z.div_pos; lia |].
    exfalso. assert ((T - F) / nZ < 0) by (apply Z.div_lt_upper_bound; nia).
    pose proof (Z.div_pos B nZ HB0 Hn). pose proof (zlen_filter_le (fun _ => true) ents).
    unfold zlen in *. lia. }
  destruct (free_slot_exists F nZ Hn (map wwZ ents) (Z.to_nat ((T - F) / nZ))) as (k & Hk & Hfree).
  { intros e He. apply in_map_iff in He as (e' & <- & _). cbn. apply w_range. }
  { rewrite Z2Nat.id by exact HKpos. rewrite zsum_map. cbn [snd wwZ].
    rewrite (zsum_add_const (fun e : word * word => bv_unsigned (snd e) / nZ) 2 ents).
    eapply Z.le_lt_trans; [| exact HK].
    assert (zsum (fun e : word * word => bv_unsigned (snd e) / nZ) ents <= B / nZ); [| lia].
    eapply Z.le_trans; [apply (zsum_div_le (fun e : word * word => bv_unsigned (snd e))); [exact Hn| intros; apply w_range]|].
    apply Z.div_le_mono; [lia|]. exact HB. }
  rewrite Z2Nat.id in Hk by exact HKpos.
  exists (F + k * nZ).
  assert (HKn : nZ * ((T - F) / nZ) <= T - F) by (apply Z.mul_div_le; lia).
  assert (Hup : F + (k + 1) * nZ <= T) by nia.
  split; [nia|]. split; [lia|]. split.
  { rewrite Z.add_mod, Z.mul_mod, Hal by (unfold page_size; lia). rewrite HFal, Z.mul_0_r.
    reflexivity. }
  split; [nia|].
  apply region_free_intro. intros st ln Hin.
  pose proof (Hfree (wwZ (st, ln)) ltac:(apply in_map_iff; exists (st, ln); auto)) as HT'. clear Hfree. rename HT' into Hfree.
  unfold touches, wwZ in Hfree. cbn [fst snd] in Hfree. unfold iv_overlap.
  rewrite !unsigned_lit' by nia.
  apply andb_false_iff. apply andb_false_iff in Hfree.
  destruct Hfree as [H|H]; apply Z.ltb_ge in H; [right| left]; apply Z.ltb_ge; nia.
Qed.

