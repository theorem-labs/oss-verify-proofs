(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
Import ListNotations.
Local Open Scope Z_scope.

Definition vlo (e : word * word) : Z := bv_unsigned (fst e).
Definition vsz (e : word * word) : Z := bv_unsigned (snd e).
Definition vhi (e : word * word) : Z := vlo e + vsz e.

Lemma vlo_nonneg e : 0 <= vlo e. Proof. unfold vlo. apply bv_unsigned_in_range. Qed.
Lemma vsz_nonneg e : 0 <= vsz e. Proof. unfold vsz. apply bv_unsigned_in_range. Qed.

Definition clear_of (g n : Z) (e : word * word) : Prop := vhi e <= g \/ g + n <= vlo e.

Fixpoint gap_cost (n c : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | e :: l' => (if c <? vhi e then vsz e + n + 4095 else 0) + gap_cost n c l'
  end.

Lemma gap_cost_nonneg n c l : 0 < n -> 0 <= gap_cost n c l.
Proof.
  intros Hn. induction l as [|e l IH]; cbn [gap_cost]; [lia|].
  pose proof (vsz_nonneg e). destruct (c <? vhi e); lia.
Qed.

Lemma gap_cost_app n c l1 l2 : gap_cost n c (l1 ++ l2) = gap_cost n c l1 + gap_cost n c l2.
Proof. induction l1 as [|e l1 IH]; cbn [gap_cost app]; [lia|]. rewrite IH. lia. Qed.

Lemma gap_cost_mono n c c' l : 0 < n -> c <= c' -> gap_cost n c' l <= gap_cost n c l.
Proof.
  intros Hn Hc. induction l as [|e l IH]; cbn [gap_cost]; [lia|].
  pose proof (vsz_nonneg e).
  destruct (Z.ltb_spec c' (vhi e)); destruct (Z.ltb_spec c (vhi e)); lia.
Qed.

Lemma gap_cost_retire n c c' l e0 :
  0 < n -> c <= c' -> In e0 l -> c < vhi e0 -> vhi e0 <= c' ->
  gap_cost n c' l + (vsz e0 + n + 4095) <= gap_cost n c l.
Proof.
  intros Hn Hc Hin Hlt Hle. induction l as [|e l IH]; [destruct Hin|]. cbn [gap_cost].
  pose proof (vsz_nonneg e). pose proof (gap_cost_mono n c c' l Hn Hc).
  destruct Hin as [->|Hin].
  - destruct (Z.ltb_spec c' (vhi e0)); destruct (Z.ltb_spec c (vhi e0)); lia.
  - specialize (IH Hin). destruct (Z.ltb_spec c' (vhi e)); destruct (Z.ltb_spec c (vhi e)); lia.
Qed.

Definition nabove (c : Z) (l : list (word * word)) : nat := length (List.filter (fun e => c <? vhi e) l).

Lemma nabove_le_length c l : (nabove c l <= length l)%nat.
Proof. unfold nabove. induction l as [|e l IH]; cbn [List.filter length]; [lia|]. destruct (c <? vhi e); cbn [length]; lia. Qed.

Lemma nabove_retire c c' l e0 :
  c <= c' -> In e0 l -> c < vhi e0 -> vhi e0 <= c' -> (nabove c' l < nabove c l)%nat.
Proof.
  intros Hc Hin Hlt Hle. unfold nabove. induction l as [|e l IH]; [destruct Hin|]. cbn [List.filter].
  assert (MONO : forall l0, (length (List.filter (fun e => Z.ltb c' (vhi e)) l0) <= length (List.filter (fun e => Z.ltb c (vhi e)) l0))%nat).
  { induction l0 as [|x l0 IH0]; cbn [List.filter]; [lia|].
    destruct (Z.ltb_spec c' (vhi x)); destruct (Z.ltb_spec c (vhi x)); cbn [length]; lia. }
  destruct Hin as [->|Hin].
  - destruct (Z.ltb_spec c' (vhi e0)); destruct (Z.ltb_spec c (vhi e0)); try lia. cbn [length]. pose proof (MONO l). lia.
  - specialize (IH Hin). destruct (Z.ltb_spec c' (vhi e)); destruct (Z.ltb_spec c (vhi e)); cbn [length]; lia.
Qed.

Lemma window_dec (c n : Z) (l : list (word * word)) :
  (forall e, In e l -> clear_of c n e) \/ (exists e0, In e0 l /\ vlo e0 < c + n /\ c < vhi e0).
Proof.
  induction l as [|e l IH].
  - left. intros e [].
  - destruct (Z.ltb_spec (vlo e) (c + n)) as [L1|L1]; [destruct (Z.ltb_spec c (vhi e)) as [L2|L2]|].
    + right. exists e. split; [left; reflexivity| split; assumption].
    + destruct IH as [IH|(e0 & F0 & F1 & F2)]; [left| right; exists e0; auto with datatypes].
      intros x [<-|Hx]; [left; lia| exact (IH x Hx)].
    + destruct IH as [IH|(e0 & F0 & F1 & F2)]; [left| right; exists e0; auto with datatypes].
      intros x [<-|Hx]; [right; lia| exact (IH x Hx)].
Qed.

Definition page_up (x : Z) : Z := ((x + 4095) / 4096) * 4096.
Lemma page_up_ge x : x <= page_up x. Proof. unfold page_up. Z.div_mod_to_equations. lia. Qed.
Lemma page_up_lt x : page_up x < x + 4096. Proof. unfold page_up. Z.div_mod_to_equations. lia. Qed.
Lemma page_up_mod x : page_up x mod 4096 = 0. Proof. unfold page_up. apply Z_mod_mult. Qed.

Lemma free_base_exists_aux : forall (k : nat) (l : list (word * word)) (c top n : Z),
  (nabove c l <= k)%nat -> 0 <= c -> c mod 4096 = 0 -> 0 < n ->
  c + n + gap_cost n c l <= top ->
  exists g, c <= g /\ g mod 4096 = 0 /\ g + n <= top /\ forall e, In e l -> clear_of g n e.
Proof.
  induction k as [|k IH]; intros l c top n Hk Hc Hal Hn Hcost.
  - destruct (window_dec c n l) as [FREE|(e0 & H0 & H1 & H2)].
    + exists c. pose proof (gap_cost_nonneg n c l Hn). repeat split; auto; lia.
    + exfalso. assert (IN : In e0 (List.filter (fun e => c <? vhi e) l)).
      { apply filter_In. split; [exact H0|]. apply Z.ltb_lt. exact H2. }
      unfold nabove in Hk. destruct (List.filter _ l); [destruct IN| cbn in Hk; lia].
  - destruct (window_dec c n l) as [FREE|(e0 & H0 & H1 & H2)].
    + exists c. pose proof (gap_cost_nonneg n c l Hn). repeat split; auto; lia.
    + set (c' := page_up (vhi e0)).
      pose proof (page_up_ge (vhi e0)) as G1. pose proof (page_up_lt (vhi e0)) as G2. fold c' in G1, G2.
      pose proof (vsz_nonneg e0) as S0.
      assert (Hcc : c <= c') by lia.
      pose proof (gap_cost_retire n c c' l e0 Hn Hcc H0 H2 G1) as RET.
      destruct (IH l c' top n) as (g & Hg1 & Hg2 & Hg3 & Hg4).
      * pose proof (nabove_retire c c' l e0 Hcc H0 H2 G1). lia.
      * lia.
      * apply page_up_mod.
      * exact Hn.
      * unfold vhi in *. lia.
      * exists g. repeat split; auto. lia.
Qed.

Theorem free_base_exists : forall (l : list (word * word)) (c top n : Z),
  0 <= c -> c mod 4096 = 0 -> 0 < n ->
  c + n + gap_cost n c l <= top ->
  exists g, c <= g /\ g mod 4096 = 0 /\ g + n <= top /\ forall e, In e l -> clear_of g n e.
Proof. intros l c top n. apply (free_base_exists_aux (nabove c l)). lia. Qed.

Fixpoint bytes_above (c : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | e :: l' => (if c <? vhi e then vsz e else 0) + bytes_above c l'
  end.

Lemma gap_cost_eq n c l : gap_cost n c l = bytes_above c l + Z.of_nat (nabove c l) * (n + 4095).
Proof.
  unfold nabove. induction l as [|e l IH]; cbn [gap_cost bytes_above List.filter length]; [lia|].
  destruct (c <? vhi e); cbn [length]; rewrite IH; lia.
Qed.

Lemma bytes_above_le_live c l : bytes_above c l <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; cbn [bytes_above live_bytes]; [lia|].
  unfold vsz; cbn [snd]. pose proof (bv_unsigned_in_range 64 sz) as [H _]. destruct (c <? _); lia.
Qed.

Lemma bytes_above_app c l1 l2 : bytes_above c (l1 ++ l2) = bytes_above c l1 + bytes_above c l2.
Proof. induction l1 as [|e l1 IH]; cbn [bytes_above app]; [lia|]. rewrite IH. lia. Qed.
Lemma nabove_app c l1 l2 : nabove c (l1 ++ l2) = (nabove c l1 + nabove c l2)%nat.
Proof. unfold nabove. rewrite List.filter_app, length_app. reflexivity. Qed.

Lemma bytes_above_low c l : (forall e, In e l -> vhi e <= c) -> bytes_above c l = 0.
Proof.
  induction l as [|e l IH]; cbn [bytes_above]; [reflexivity|]. intros H.
  destruct (Z.ltb_spec c (vhi e)); [pose proof (H e (or_introl eq_refl)); lia|]. rewrite IH; [lia|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma nabove_low c l : (forall e, In e l -> vhi e <= c) -> nabove c l = 0%nat.
Proof.
  unfold nabove. induction l as [|e l IH]; cbn [List.filter]; [reflexivity|]. intros H.
  destruct (Z.ltb_spec c (vhi e)); [pose proof (H e (or_introl eq_refl)); lia|]. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma nabove_of_minsize c l m : 0 < m -> (forall e, In e l -> c < vhi e -> m <= vsz e) ->
  Z.of_nat (nabove c l) * m <= bytes_above c l.
Proof.
  intros Hm H. unfold nabove. induction l as [|e l IH]; cbn [List.filter bytes_above length]; [lia|].
  specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)).
  destruct (Z.ltb_spec c (vhi e)); cbn [length]; [| lia].
  pose proof (H e (or_introl eq_refl) ltac:(assumption)). lia.
Qed.

Lemma nabove_of_cover c l (cover : list (word * word)) :
  List.NoDup (List.filter (fun e => c <? vhi e) l) ->
  (forall e, In e l -> c < vhi e -> In e cover) ->
  (nabove c l <= length cover)%nat.
Proof.
  intros ND H. unfold nabove. apply List.NoDup_incl_length; [exact ND|].
  intros e He. apply filter_In in He as [He Hc]. apply H; [exact He|]. apply Z.ltb_lt. exact Hc.
Qed.

Lemma gap_cost_le n c l B N : 0 < n ->
  bytes_above c l <= B -> (Z.of_nat (nabove c l) <= N) ->
  gap_cost n c l <= B + N * (n + 4095).
Proof. intros Hn HB HN. rewrite gap_cost_eq. nia. Qed.

Lemma region_free_of_clear maps g n :
  0 <= g -> 0 <= n -> g + n < 2^64 ->
  (forall e, In e maps -> clear_of g n e) ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 n) = true.
Proof.
  intros Hg Hn Hgn H. induction maps as [|[a sz] maps IH]; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e He; apply H; right; exact He).
  specialize (H (a, sz) (or_introl eq_refl)). unfold clear_of, vhi, vlo, vsz in H; cbn [fst snd] in H.
  unfold iv_overlap. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  destruct (Z.ltb_spec g (bv_unsigned a + bv_unsigned sz)); destruct (Z.ltb_spec (bv_unsigned a) (g + n)); cbn; try reflexivity. lia.
Qed.

Theorem vm_gap_available_of_cost : forall h nZ c,
  0 < c -> c mod 4096 = 0 -> 0 < nZ ->
  c + nZ + gap_cost nZ c (vm_reserved h ++ vm_maps h) <= alloc_top h ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ c Hc Hal Hn Hcost. pose proof (alloc_top_lt h) as TOP. unfold two_pow_64 in TOP.
  destruct (free_base_exists (vm_reserved h ++ vm_maps h) c (alloc_top h) nZ ltac:(lia) Hal Hn Hcost) as (g & G1 & G2 & G3 & G4).
  apply vm_gap_available_iff. exists (Z_to_bv 64 g).
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  change page_size with 4096.
  split; [exact G2|]. split; [lia|]. split; [exact G3|].
  apply region_free_of_clear; [lia| lia| lia| exact G4].
Qed.
