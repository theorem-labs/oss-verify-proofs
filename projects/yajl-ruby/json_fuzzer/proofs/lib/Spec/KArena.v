(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc KInv KLink KStep KStepX KLive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section PIGEON.
  Variables (F n : Z).
  Hypothesis Hn : 0 < n.

  Definition cand (j : nat) : Z := F + Z.of_nat j * n.
  (* [comment removed for export] *)
  Definition conf (e : Z * Z) (c : Z) : bool := (fst e <? c + n) && (c <? snd e).
  (* [comment removed for export] *)
  Definition freeb (E : list (Z * Z * Z)) (c : Z) : bool := forallb (fun ek => negb (conf (fst ek) c)) E.
  Fixpoint csum (E : list (Z * Z * Z)) : Z := match E with [] => 0 | ek :: E' => snd ek + csum E' end.

  Fixpoint spaced (l : list Z) : Prop :=
    match l with [] => True | x :: l' => (forall y, In y l' -> x + n <= y) /\ spaced l' end.

  Lemma spaced_filter p l : spaced l -> spaced (List.filter p l).
  Proof.
    induction l as [|x l IH]; cbn; [trivial|]. intros [H1 H2].
    destruct (p x); cbn; [| exact (IH H2)]. split; [| exact (IH H2)].
    intros y Hy. apply List.filter_In in Hy as [Hy _]. exact (H1 y Hy).
  Qed.

  Lemma spaced_cands j0 m : spaced (map cand (seq j0 m)).
  Proof.
    revert j0. induction m as [|m IH]; intros j0; cbn; [trivial|]. split; [| apply IH].
    intros y Hy. apply in_map_iff in Hy as (j & <- & Hj). apply in_seq in Hj. unfold cand.
    assert (Z.of_nat j0 + 1 <= Z.of_nat j) by lia. nia.
  Qed.

  Lemma spaced_span l a b : spaced l -> (forall x, In x l -> a <= x <= b) -> l <> [] ->
    (Z.of_nat (length l) - 1) * n <= b - a.
  Proof.
    revert a. induction l as [|x l IH]; intros a Hs Hin Hne; [congruence|]. destruct Hs as [H1 H2].
    pose proof (Hin x (or_introl eq_refl)) as Hx.
    destruct l as [|y l'].
    - cbn [length]. lia.
    - assert (IH' : (Z.of_nat (length (y :: l')) - 1) * n <= b - (x + n)).
      { apply IH; [exact H2| | congruence]. intros z Hz. split; [apply H1; exact Hz| apply (Hin z); right; exact Hz]. }
      cbn [length] in *. rewrite Nat2Z.inj_succ in *. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma count_conf_gen e m :
    Z.of_nat (length (List.filter (conf e) (map cand (seq 0 m)))) <= Z.max 0 (snd e - fst e) / n + 2.
  Proof.
    set (A := List.filter (conf e) (map cand (seq 0 m))).
    pose proof (Z.div_pos (Z.max 0 (snd e - fst e)) n ltac:(lia) Hn) as P0.
    destruct A as [|x l] eqn:EA; [cbn; lia|].
    assert (HS : spaced A) by (subst A; apply spaced_filter, spaced_cands).
    assert (HB : forall y, In y A -> fst e - n + 1 <= y <= snd e - 1).
    { intros y Hy. subst A. apply List.filter_In in Hy as [_ Hc]. unfold conf in Hc. apply andb_prop in Hc as [C1 C2].
      apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. lia. }
    rewrite EA in HS, HB. pose proof (spaced_span (x :: l) _ _ HS HB ltac:(congruence)) as SP.
    enough (Z.of_nat (length (x :: l)) - 2 <= Z.max 0 (snd e - fst e) / n) by lia.
    apply Z.div_le_lower_bound; [exact Hn|]. nia.
  Qed.

  Lemma lt_aligned a b P : 0 < P -> a mod P = 0 -> b mod P = 0 -> a < b -> a + P <= b.
  Proof.
    intros HP Ha Hb Hab. pose proof (Z_div_mod_eq_full a P) as Ea. pose proof (Z_div_mod_eq_full b P) as Eb.
    rewrite Ha in Ea. rewrite Hb in Eb.
    assert (a / P + 1 <= b / P) by nia. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma count_conf_pg PG e m : 0 < PG -> PG <= n -> F mod PG = 0 -> n mod PG = 0 ->
    fst e mod PG = 0 -> snd e mod PG = 0 -> fst e < snd e ->
    Z.of_nat (length (List.filter (conf e) (map cand (seq 0 m)))) <= (snd e - fst e) / PG.
  Proof.
    intros HP HPn HF HnP Hlo Hhi Hlt.
    set (A := List.filter (conf e) (map cand (seq 0 m))).
    pose proof (lt_aligned _ _ _ HP Hlo Hhi Hlt) as Hlen.
    assert (P1 : 1 <= (snd e - fst e) / PG) by (apply Z.div_le_lower_bound; lia).
    destruct A as [|x l] eqn:EA; [cbn; lia|].
    assert (HS : spaced A) by (subst A; apply spaced_filter, spaced_cands).
    assert (HC : forall y, In y A -> y mod PG = 0 /\ fst e < y + n /\ y < snd e).
    { intros y Hy. subst A. apply List.filter_In in Hy as [Hy Hc]. unfold conf in Hc. apply andb_prop in Hc as [C1 C2].
      apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. split; [| split; [exact C1| exact C2]].
      apply in_map_iff in Hy as (j & <- & _). unfold cand.
      rewrite Z.add_mod, HF, Z.mul_mod, HnP, Z.mul_0_r, (Z.mod_0_l PG) by lia. reflexivity. }
    assert (HB : forall y, In y A -> fst e + PG - n <= y <= snd e - PG).
    { intros y Hy. destruct (HC y Hy) as (M & C1 & C2).
      pose proof (lt_aligned _ _ _ HP Hlo ltac:(rewrite Z.add_mod, M, HnP by lia; reflexivity) C1).
      pose proof (lt_aligned _ _ _ HP M Hhi C2). lia. }
    rewrite EA in HS, HB. pose proof (spaced_span (x :: l) _ _ HS HB ltac:(congruence)) as SP.
    set (k := Z.of_nat (length (x :: l))) in *. set (d := snd e - fst e) in *.
    destruct (Z.le_gt_cases k (d / PG)) as [|Hgt]; [assumption| exfalso].
    set (p := d / PG) in *.
    assert (Hdm : d mod PG = 0) by (subst d; rewrite Zminus_mod, Hlo, Hhi; cbn; apply Z.mod_0_l; lia).
    pose proof (Z_div_mod_eq_full d PG) as Ed. rewrite Hdm in Ed. fold p in Ed.
    assert (H1 : (p - 1) * n <= (k - 2) * n) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (H2 : (p - 1) * PG <= (p - 1) * n) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
  Qed.

  Lemma length_filter_and {A} (p q : A -> bool) (l : list A) :
    (length (List.filter q l) <= length (List.filter (fun x => p x && q x) l) + length (List.filter (fun x => negb (p x)) l))%nat.
  Proof. induction l as [|a l IH]; cbn; [lia|]. destruct (p a), (q a); cbn; lia. Qed.

  Lemma free_count E m :
    (forall ek, In ek E -> Z.of_nat (length (List.filter (conf (fst ek)) (map cand (seq 0 m)))) <= snd ek) ->
    Z.of_nat m - csum E <= Z.of_nat (length (List.filter (freeb E) (map cand (seq 0 m)))).
  Proof.
    induction E as [|ek E IH]; intros Hc.
    - cbn [csum]. rewrite forallb_filter_id by (apply forallb_forall; intros; reflexivity). rewrite length_map, length_seq. lia.
    - cbn [csum]. specialize (IH ltac:(intros e' He'; apply Hc; right; exact He')).
      pose proof (Hc ek (or_introl eq_refl)) as He.
      pose proof (length_filter_and (fun c => negb (conf (fst ek) c)) (freeb E) (map cand (seq 0 m))) as L.
      change (List.filter (freeb (ek :: E)) (map cand (seq 0 m))) with (List.filter (fun c => negb (conf (fst ek) c) && freeb E c) (map cand (seq 0 m))).
      rewrite (filter_ext_in (fun x => negb (negb (conf (fst ek) x))) (conf (fst ek))) in L by (intros; apply negb_involutive).
      lia.
  Qed.

  Theorem pigeon E m :
    (forall ek, In ek E -> Z.of_nat (length (List.filter (conf (fst ek)) (map cand (seq 0 m)))) <= snd ek) ->
    csum E < Z.of_nat m ->
    exists j, (j < m)%nat /\ forall ek, In ek E -> cand j + n <= fst (fst ek) \/ snd (fst ek) <= cand j.
  Proof.
    intros Hc Hlt. pose proof (free_count E m Hc) as FC.
    destruct (List.filter (freeb E) (map cand (seq 0 m))) as [|c l] eqn:EF; [cbn in FC; lia|].
    assert (Hin : In c (List.filter (freeb E) (map cand (seq 0 m)))) by (rewrite EF; left; reflexivity).
    apply List.filter_In in Hin as [Hin Hf]. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
    exists j. split; [lia|]. intros ek He. unfold freeb in Hf. pose proof (proj1 (forallb_forall _ _) Hf ek He) as Hf'. clear Hf. rename Hf' into Hf. cbn beta in Hf.
    unfold conf in Hf. apply negb_true_iff in Hf. apply andb_false_iff in Hf as [Hf|Hf]; apply Z.ltb_ge in Hf; lia.
  Qed.
End PIGEON.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma csum_app A B : csum (A ++ B) = csum A + csum B.
Proof. induction A as [|x A IH]; cbn; [lia| rewrite IH; lia]. Qed.

Definition ecostR (e : word * word) : Z := bv_unsigned (snd e) / PGSZ + 2.
Fixpoint rcost (R : list (word * word)) : Z := match R with [] => 0 | e :: R' => ecostR e + rcost R' end.

Lemma rcost_nonneg R : 0 <= rcost R.
Proof.
  induction R as [|e R IH]; cbn; [lia|]. unfold ecostR.
  pose proof (Z.div_pos (bv_unsigned (snd e)) PGSZ ltac:(pose proof (bv_unsigned_in_range 64 (snd e)); lia) ltac:(unfold PGSZ; lia)). lia.
Qed.

Lemma sum_div_le (l : list Z) P : 0 < P -> Forall (fun z => 0 <= z) l ->
  fold_right (fun z acc => z / P + acc) 0 l <= fold_right Z.add 0 l / P.
Proof.
  intros HP. induction 1 as [|z l Hz Hl IH]; cbn; [rewrite Z.div_0_l; lia|].
  assert (F0 : 0 <= fold_right Z.add 0 l) by (clear IH; induction Hl; cbn; lia).
  apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le z P HP). pose proof (Z.mul_div_le (fold_right Z.add 0 l) P HP).
  pose proof (Z.div_pos (fold_right Z.add 0 l) P F0 HP). nia.
Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000. Proof. reflexivity. Qed.
Lemma bottomup_floor_facts : bottomup_floor mod 4096 = 0 /\ 0 < bottomup_floor < alloc_ceiling.
Proof. unfold bottomup_floor, alloc_ceiling. split; [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Theorem KL_arena_gen : forall F L pbrk mo len,
  F mod 4096 = 0 -> 0 < F < alloc_ceiling ->
  KL L pbrk mo -> 0 < len ->
  let h := m_vmmaps mo in
  let n := mmap_len len in
  n * (live_bytes (vm_maps h) / PGSZ + rcost (vm_reserved h) + 1) <= alloc_ceiling - F ->
  exists r, (r mod 4096 = 0 /\ 0 < r /\ r + n <= alloc_ceiling) /\ F <= r
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 r) (Z_to_bv 64 n) = true.
Proof.
  intros F L pbrk mo len F1 [F2 F3] HK Hlen h n Hbud.
  pose proof alloc_ceiling_lt as Hcl.
  pose proof (mmap_len_ge len Hlen) as N1. pose proof (mmap_len_aligned len) as N2. fold n in N1, N2.
  assert (N3 : 4096 <= n) by (pose proof (lt_aligned 0 n 4096 ltac:(lia) eq_refl N2 ltac:(lia)); lia).
  pose proof (live_bytes_nonneg (vm_maps h)) as LB0. pose proof (rcost_nonneg (vm_reserved h)) as RC0.
  assert (Npos : 0 < n) by lia.
  set (W := alloc_ceiling - F) in *.
  set (m := Z.to_nat (W / n)).
  assert (HmW : Z.of_nat m * n <= W) by (subst m; rewrite Z2Nat.id by (apply Z.div_pos; lia); pose proof (Z.mul_div_le W n Npos); lia).
  (* [comment removed for export] *)
  set (ER := map (fun e => ((elo e, ehi e), ecostR e)) (vm_reserved h)).
  set (EM := map (fun e => ((elo e, ehi e), bv_unsigned (snd e) / PGSZ)) (vm_maps h)).
  assert (CR : csum ER = rcost (vm_reserved h)) by (subst ER; clear; induction (vm_reserved h) as [|e R IH]; cbn; [reflexivity| rewrite IH; reflexivity]).
  assert (CM : csum EM <= live_bytes (vm_maps h) / PGSZ).
  { subst EM. clear -LB0. induction (vm_maps h) as [|[a sz] M IH]; cbn; [rewrite Z.div_0_l; unfold PGSZ; lia|].
    cbn in LB0. pose proof (live_bytes_nonneg M) as M0. pose proof (bv_unsigned_in_range 64 sz) as S0. specialize (IH M0).
    unfold PGSZ in *.
    pose proof (Z.mul_div_le (bv_unsigned sz) 4096 ltac:(lia)). pose proof (Z.mul_div_le (live_bytes M) 4096 ltac:(lia)).
    pose proof (Z.div_pos (live_bytes M) 4096 M0 ltac:(lia)). pose proof (Z.div_pos (bv_unsigned sz) 4096 ltac:(lia) ltac:(lia)).
    apply Z.div_le_lower_bound; [lia|]. lia. }
  assert (Hcnt : forall ek, In ek (ER ++ EM) -> Z.of_nat (length (List.filter (conf n (fst ek)) (map (cand F n) (seq 0 m)))) <= snd ek).
  { intros ek Hin. apply in_app_or in Hin as [Hin|Hin].
    - subst ER. apply in_map_iff in Hin as (e & <- & He). cbn [fst snd].
      etransitivity; [apply count_conf_gen; lia|]. unfold ecostR. cbn [fst snd].
      unfold ehi. replace (Z.max 0 (elo e + bv_unsigned (snd e) - elo e)) with (bv_unsigned (snd e)) by (pose proof (bv_unsigned_in_range 64 (snd e)); lia).
      pose proof (Z.div_le_compat_l (bv_unsigned (snd e)) PGSZ n ltac:(pose proof (bv_unsigned_in_range 64 (snd e)); lia) ltac:(unfold PGSZ; lia)). lia.
    - subst EM. apply in_map_iff in Hin as (e & <- & He). cbn [fst snd].
      destruct (kl_pages _ _ _ HK e He) as [P1 P2]. pose proof (proj1 (kl_wf _ _ _ HK) e He) as W1. fold h in P1, P2, W1.
      etransitivity; [apply (count_conf_pg F n Npos PGSZ); unfold PGSZ in *; cbn [fst snd]; try lia; assumption|].
      cbn [fst snd]. unfold ehi. replace (elo e + bv_unsigned (snd e) - elo e) with (bv_unsigned (snd e)) by lia. lia. }
  destruct (pigeon F n (ER ++ EM) m Hcnt) as (j & Hj & Hfree).
  { rewrite csum_app.
    rewrite CR. apply (Z.le_lt_trans _ (live_bytes (vm_maps h) / PGSZ + rcost (vm_reserved h))); [lia|].
    enough (live_bytes (vm_maps h) / PGSZ + rcost (vm_reserved h) + 1 <= W / n) by (subst m; rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
    apply Z.div_le_lower_bound; [lia|]. lia. }
  set (r := cand F n j) in *. unfold cand in r.
  assert (Hr1 : F <= r /\ r + n <= alloc_ceiling).
  { assert (Hjm : Z.of_nat j + 1 <= Z.of_nat m) by (clear -Hj; lia).
    subst r W. clear -Hjm HmW Npos F2. split; nia. }
  assert (Hr2 : r mod 4096 = 0) by (subst r; rewrite Z.add_mod, F1, Z.mul_mod, N2, Z.mul_0_r by lia; reflexivity).
  exists r. split; [split; [exact Hr2| lia]|]. split; [lia|].
  apply region_free_of_disj. rewrite !unsigned_lit by lia.
  intros e He. apply in_app_or in He as [He|He].
  - specialize (Hfree ((elo e, ehi e), ecostR e) ltac:(apply in_or_app; left; subst ER; apply in_map_iff; exists e; auto)). cbn [fst snd] in Hfree. lia.
  - specialize (Hfree ((elo e, ehi e), bv_unsigned (snd e) / PGSZ) ltac:(apply in_or_app; right; subst EM; apply in_map_iff; exists e; auto)). cbn [fst snd] in Hfree. lia.
Qed.

Theorem KL_arena : forall L pbrk mo len,
  KL L pbrk mo -> 0 < len ->
  let h := m_vmmaps mo in
  let n := mmap_len len in
  n * (live_bytes (vm_maps h) / PGSZ + rcost (vm_reserved h) + 1) <= alloc_ceiling - bottomup_floor ->
  exists r, (r mod 4096 = 0 /\ 0 < r /\ r + n <= alloc_ceiling) /\ bottomup_floor <= r
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 r) (Z_to_bv 64 n) = true.
Proof.
  pose proof bottomup_floor_facts as [F1 F23]. intros L pbrk mo len HK Hlen. exact (KL_arena_gen bottomup_floor L pbrk mo len F1 F23 HK Hlen).
Qed.
End RC__1.
