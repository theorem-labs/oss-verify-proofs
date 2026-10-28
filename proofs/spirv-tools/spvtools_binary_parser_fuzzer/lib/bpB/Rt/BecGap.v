(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BKInv BapGrid.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bap04 BazyRestrict BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint zrange (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S k => lo :: zrange (lo + 1) k end.

Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1; intros; cbn; [reflexivity| rewrite IHl1; lia]. Qed.
Lemma zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= zsum l.
Proof. induction l; intros H; cbn; [lia|]. inversion H; subst. specialize (IHl ltac:(assumption)). lia. Qed.

Section Grid.
  Variables (B M S : Z) (J : Z).
  Hypothesis HM : 0 < M. Hypothesis HS : 0 < S <= M.

  Definition gslot (i : Z) : Z := B + i * M.

  Definition c1 (e : word * word) : Z := Z.max 0 ((elo e - S - B) / M + 1).
  Definition c2 (e : word * word) : Z := (ehi e - 1 - B) / M.
  Definition nblk (e : word * word) : Z := Z.max 0 (c2 e - c1 e + 1).
  Definition blocked (e : word * word) : list Z := zrange (c1 e) (Z.to_nat (nblk e)).

  Definition gload (E : list (word * word)) : Z := zsum (map nblk E).

End Grid.

Section Scan.
  Variable n : Z.
  Hypothesis Hn : 0 < n.

  Definition ecost (g : Z) (e : word * word) : Z := if g <? ehi e then ehi e - elo e + n + 4096 else 0.
  Definition cost (g : Z) (E : list (word * word)) : Z := zsum (map (ecost g) E).
  Fixpoint above (g : Z) (E : list (word * word)) : nat :=
    match E with [] => 0%nat | e :: E' => ((if (g <? ehi e)%Z then 1 else 0) + above g E')%nat end.

  Lemma ecost_nonneg : forall g e, 0 <= ecost g e.
  Proof. intros g e. unfold ecost, ehi, elo. pose proof (bv_unsigned_in_range 64 (snd e)). destruct (g <? _); lia. Qed.
  Lemma cost_nonneg : forall g E, 0 <= cost g E.
  Proof. intros g E. unfold cost. apply zsum_nonneg. apply Forall_map, Forall_forall. intros; apply ecost_nonneg. Qed.
  Lemma cost_app : forall g E1 E2, cost g (E1 ++ E2) = cost g E1 + cost g E2.
  Proof. intros. unfold cost. rewrite map_app, zsum_app. reflexivity. Qed.
  Lemma cost_cons : forall g e E, cost g (e :: E) = ecost g e + cost g E.
  Proof. reflexivity. Qed.
  Lemma cost_nil : forall g, cost g [] = 0.
  Proof. reflexivity. Qed.
  Lemma ecost_below : forall g e, ehi e <= g -> ecost g e = 0.
  Proof. intros g e H. unfold ecost. destruct (Z.ltb_spec g (ehi e)); [lia| reflexivity]. Qed.

  Lemma ecost_mono : forall g g' e, g <= g' -> ecost g' e <= ecost g e.
  Proof.
    intros g g' e H. unfold ecost, ehi, elo. pose proof (bv_unsigned_in_range 64 (snd e)).
    destruct (Z.ltb_spec g' (bv_unsigned (fst e) + bv_unsigned (snd e))); destruct (Z.ltb_spec g (bv_unsigned (fst e) + bv_unsigned (snd e))); lia.
  Qed.
  Lemma cost_mono : forall g g' E, g <= g' -> cost g' E <= cost g E.
  Proof. intros g g' E H. induction E as [|e E IH]; [cbn; lia|]. rewrite !cost_cons. pose proof (ecost_mono g g' e H). lia. Qed.
  Lemma above_mono : forall g g' E, g <= g' -> (above g' E <= above g E)%nat.
  Proof.
    intros g g' E H. induction E as [|e E IH]; [cbn; lia|]. cbn [above].
    destruct (Z.ltb_spec g' (ehi e)); destruct (Z.ltb_spec g (ehi e)); lia.
  Qed.
  Lemma above_zero : forall g E, above g E = 0%nat -> forall e, In e E -> ehi e <= g.
  Proof.
    intros g E. induction E as [|e0 E IH]; intros H e He; [destruct He|]. cbn [above] in H.
    destruct (Z.ltb_spec g (ehi e0)); [lia|]. destruct He as [<-|He]; [lia| apply IH; [lia| exact He]].
  Qed.

  Lemma scan_step : forall g E e0, In e0 E -> g < ehi e0 -> elo e0 < g + n ->
    let g' := page_round_up_Z (ehi e0) in
    g < g' /\ (above g' E < above g E)%nat /\ g' + cost g' E <= g + cost g E.
  Proof.
    intros g E e0 IN H1 H2. cbv zeta.
    pose proof (BlacementSearch.page_round_up_Z_ge (ehi e0)) as U1.
    assert (U2 : page_round_up_Z (ehi e0) < ehi e0 + 4096) by (unfold page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    set (g' := page_round_up_Z (ehi e0)) in *. split; [lia|].
    induction E as [|e E IH]; [destruct IN|].
    destruct IN as [<-|IN].
    -
      cbn [above]. rewrite !cost_cons.
      pose proof (above_mono g g' E ltac:(lia)). pose proof (cost_mono g g' E ltac:(lia)).
      unfold ecost. destruct (Z.ltb_spec g' (ehi e)); [lia|]. destruct (Z.ltb_spec g (ehi e)); [|lia]. lia.
    - specialize (IH IN). destruct IH as [IH1 IH2].
      cbn [above]. rewrite !cost_cons. pose proof (ecost_mono g g' e ltac:(lia)).
      destruct (Z.ltb_spec g' (ehi e)); destruct (Z.ltb_spec g (ehi e)); lia.
  Qed.

  Lemma first_fit_k : forall (k : nat) (E : list (word * word)) (g T : Z),
    (above g E <= k)%nat -> 0 <= g -> g mod 4096 = 0 -> g + cost g E + n <= T ->
    exists a, a mod 4096 = 0 /\ g <= a /\ a + n <= T /\ forall e, In e E -> a + n <= elo e \/ ehi e <= a.
  Proof.
    induction k as [|k IH]; intros E g T HK G0 GA BND.
    - exists g. pose proof (cost_nonneg g E). split; [exact GA|]. split; [lia|]. split; [lia|].
      intros e He. right. apply (above_zero g E); [lia| exact He].
    - destruct (List.find (fun e => (g <? ehi e) && (elo e <? g + n)) E) as [e0|] eqn:FD.
      + apply find_some in FD. destruct FD as [IN C]. apply andb_true_iff in C. destruct C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
        destruct (scan_step g E e0 IN C1 C2) as (S1 & S2 & S3).
        destruct (IH E (page_round_up_Z (ehi e0)) T ltac:(lia) ltac:(lia) ltac:(unfold page_round_up_Z, page_size; apply Z_mod_mult) ltac:(lia))
          as (a & A1 & A2 & A3 & A4).
        exists a. split; [exact A1|]. split; [lia|]. split; [exact A3| exact A4].
      + exists g. pose proof (cost_nonneg g E). split; [exact GA|]. split; [lia|]. split; [lia|].
        intros e He. pose proof (find_none _ _ FD e He) as X. cbn beta in X. apply andb_false_iff in X.
        destruct X as [X|X]; [right; apply Z.ltb_ge in X; lia| left; apply Z.ltb_ge in X; lia].
  Qed.

  Theorem first_fit : forall (E : list (word * word)) (g T : Z),
    0 <= g -> g mod 4096 = 0 -> g + cost g E + n <= T ->
    exists a, a mod 4096 = 0 /\ g <= a /\ a + n <= T /\ forall e, In e E -> a + n <= elo e \/ ehi e <= a.
  Proof. intros E g T. apply (first_fit_k (above g E)). lia. Qed.
End Scan.

Theorem gap_witness_fit : forall (h : VmMaps) (B T n : Z),
  0 < n -> 0 < B -> B mod 4096 = 0 -> T < 2^64 ->
  B + cost n B (vm_reserved h ++ vm_maps h) + n <= T ->
  exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ B <= bv_unsigned g /\ bv_unsigned g + n <= T
                   /\ region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 n) = true.
Proof.
  intros h B T n Hn HB HBal HT BND.
  destruct (first_fit n Hn (vm_reserved h ++ vm_maps h) B T ltac:(lia) HBal BND) as (a & A1 & A2 & A3 & A4).
  pose proof (cost_nonneg n Hn B (vm_reserved h ++ vm_maps h)) as CN.
  exists (Z_to_bv 64 a). rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  split; [unfold page_size; exact A1|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply region_free_introZ. intros e sz He. specialize (A4 (e, sz) He). unfold elo, ehi in A4. cbn [fst snd] in A4.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

Corollary gap_witness_fit_top : forall (h : VmMaps) (B n : Z),
  0 < n -> 0 < B -> B mod 4096 = 0 -> alloc_top h < 2^64 ->
  B + cost n B (vm_reserved h ++ vm_maps h) + n <= alloc_top h ->
  exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + n <= alloc_top h
                   /\ region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 n) = true.
Proof.
  intros h B n Hn HB HBal HT BND.
  destruct (gap_witness_fit h B (alloc_top h) n Hn HB HBal HT BND) as (g & G1 & G2 & G3 & G4 & G5).
  exists g. repeat split; assumption.
Qed.
