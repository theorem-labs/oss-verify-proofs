(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import KInv GapGrid.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Gap04 LazyRestrict LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint zrange (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S k => lo :: zrange (lo + 1) k end.
Lemma zrange_length : forall lo n, length (zrange lo n) = n.
Proof. intros lo n. revert lo. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma in_zrange : forall i lo n, lo <= i < lo + Z.of_nat n -> In i (zrange lo n).
Proof.
  intros i lo n. revert lo. induction n as [|n IH]; intros lo H; [lia|]. cbn.
  destruct (Z.eq_dec lo i); [left; exact e| right]. apply IH. lia.
Qed.

Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1; intros; cbn; [reflexivity| rewrite IHl1; lia]. Qed.
Lemma zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= zsum l.
Proof. induction l; intros H; cbn; [lia|]. inversion H; subst. specialize (IHl ltac:(assumption)). lia. Qed.

(* [comment removed for export] *)
Section Grid.
  Variables (B M S : Z) (J : Z).
  Hypothesis HM : 0 < M. Hypothesis HS : 0 < S <= M.

  Definition gslot (i : Z) : Z := B + i * M.
  (* [comment removed for export] *)
  Definition c1 (e : word * word) : Z := Z.max 0 ((elo e - S - B) / M + 1).
  Definition c2 (e : word * word) : Z := (ehi e - 1 - B) / M.
  Definition nblk (e : word * word) : Z := Z.max 0 (c2 e - c1 e + 1).
  Definition blocked (e : word * word) : list Z := zrange (c1 e) (Z.to_nat (nblk e)).

  Lemma meets_blocked : forall e i, 0 <= i -> elo e < gslot i + S -> gslot i < ehi e -> In i (blocked e).
  Proof.
    intros e i Hi H1 H2. unfold blocked, nblk, c1, c2, gslot in *. apply in_zrange.
    assert (A : (elo e - S - B) / M + 1 <= i) by (apply Zlt_le_succ_r_iff || idtac; Z.div_mod_to_equations; nia).
    assert (C : i <= (ehi e - 1 - B) / M) by (Z.div_mod_to_equations; (first [clear - H0 H H2 HS; nia | nia])).
    rewrite Z2Nat.id by (first [clear - HM; lia | lia]). (first [clear - C A Hi HM; lia | lia]).
  Qed.

  Lemma blocked_length : forall e, Z.of_nat (length (blocked e)) = nblk e.
  Proof. intros e. unfold blocked. rewrite zrange_length, Z2Nat.id; [reflexivity|]. unfold nblk. lia. Qed.

  (* [comment removed for export] *)
  Definition gload (E : list (word * word)) : Z := zsum (map nblk E).

  Lemma gload_app : forall E1 E2, gload (E1 ++ E2) = gload E1 + gload E2.
  Proof. intros. unfold gload. rewrite map_app, zsum_app. reflexivity. Qed.
  Lemma gload_cons : forall e E, gload (e :: E) = nblk e + gload E.
  Proof. reflexivity. Qed.
  Lemma nblk_nonneg : forall e, 0 <= nblk e.
  Proof. intros. unfold nblk. lia. Qed.
  Lemma gload_nonneg : forall E, 0 <= gload E.
  Proof. intros. unfold gload. apply zsum_nonneg. apply Forall_map. apply Forall_forall. intros; apply nblk_nonneg. Qed.

  (* [comment removed for export] *)
  Lemma nblk_below : forall e, ehi e <= B -> nblk e = 0.
  Proof. intros e H. unfold nblk, c1, c2. Z.div_mod_to_equations. nia. Qed.
  Lemma nblk_le : forall e, elo e <= ehi e -> nblk e <= (ehi e - elo e) / M + 3.
  Proof using B M S HM HS. intros e H. unfold nblk, c1, c2. Z.div_mod_to_equations. (first [clear - H11 H10 H6 H5 H1 H0 H HS; nia | nia]). Qed.

  Lemma flat_blocked_length : forall E, Z.of_nat (length (flat_map blocked E)) = gload E.
  Proof. induction E as [|e E IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, Nat2Z.inj_add, blocked_length, IH. reflexivity. Qed.

  Theorem grid_gap_gen : forall E, 0 <= J -> gload E < J ->
    exists i, 0 <= i < J /\ forall e, In e E -> gslot i + S <= elo e \/ ehi e <= gslot i.
  Proof.
    intros E HJ HL. pose proof (flat_blocked_length E) as LEN.
    set (bl := flat_map blocked E) in *.
    destruct (pigeon (Z.to_nat J) bl ltac:(lia)) as (i & Hi & Hni). rewrite Z2Nat.id in Hi by lia.
    exists i. split; [exact Hi|]. intros e He.
    destruct (Z.le_gt_cases (gslot i + S) (elo e)); [left; lia|].
    destruct (Z.le_gt_cases (ehi e) (gslot i)); [right; lia|].
    exfalso. apply Hni. subst bl. apply in_flat_map. exists e. split; [exact He|]. apply meets_blocked; lia.
  Qed.
End Grid.

(* [comment removed for export] *)
Theorem gap_witness : forall (h : VmMaps) (B T M J n : Z),
  0 < M -> M mod 4096 = 0 -> 0 <= J -> 0 < B -> B mod 4096 = 0 -> B + J * M <= T -> T < 2^64 ->
  0 < n <= M ->
  gload B M n (vm_reserved h ++ vm_maps h) < J ->
  exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ B <= bv_unsigned g /\ bv_unsigned g + n <= T
                   /\ region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 n) = true.
Proof.
  intros h B T M J n HM HMal HJ HB HBal BAND HT Hn HL.
  destruct (grid_gap_gen B M n J HM Hn _ HJ HL) as (i & Hi & FREE). unfold gslot in FREE.
  assert (R : B <= B + i * M /\ B + i * M + n <= T) by nia.
  exists (Z_to_bv 64 (B + i * M)). rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  split; [| split; [lia| split; [lia| split; [lia|]]]].
  - unfold page_size. rewrite Z.add_mod, Z.mul_mod, HMal, Z.mul_0_r, Z.mod_0_l, Z.add_0_r, Z.mod_mod by lia. exact HBal.
  - apply region_free_introZ. intros e sz He. specialize (FREE (e, sz) He). unfold elo, ehi in FREE. cbn [fst snd] in FREE.
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

(* [comment removed for export] *)
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
  Lemma ecost_le : forall g e, ecost g e <= ehi e - elo e + n + 4096.
  Proof. intros g e. unfold ecost, ehi, elo. pose proof (bv_unsigned_in_range 64 (snd e)). destruct (g <? _); lia. Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma scan_step : forall g E e0, In e0 E -> g < ehi e0 -> elo e0 < g + n ->
    let g' := page_round_up_Z (ehi e0) in
    g < g' /\ (above g' E < above g E)%nat /\ g' + cost g' E <= g + cost g E.
  Proof.
    intros g E e0 IN H1 H2. cbv zeta.
    pose proof (PlacementSearch.page_round_up_Z_ge (ehi e0)) as U1.
    assert (U2 : page_round_up_Z (ehi e0) < ehi e0 + 4096) by (unfold page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    set (g' := page_round_up_Z (ehi e0)) in *. split; [lia|].
    induction E as [|e E IH]; [destruct IN|].
    destruct IN as [<-|IN].
    - (* [comment removed for export] *)
      cbn [above]. rewrite !cost_cons.
      pose proof (above_mono g g' E ltac:(lia)). pose proof (cost_mono g g' E ltac:(lia)).
      unfold ecost. destruct (Z.ltb_spec g' (ehi e)); [lia|]. destruct (Z.ltb_spec g (ehi e)); [|lia]. lia.
    - specialize (IH IN). destruct IH as [IH1 IH2].
      cbn [above]. rewrite !cost_cons. pose proof (ecost_mono g g' e ltac:(lia)).
      destruct (Z.ltb_spec g' (ehi e)); destruct (Z.ltb_spec g (ehi e)); lia.
  Qed.

  (* [comment removed for export] *)
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

Lemma cost_mono_n : forall n n' g E, n <= n' -> cost n g E <= cost n' g E.
Proof. intros n n' g E H. induction E as [|e E IH]; [cbn; lia|]. rewrite !cost_cons. unfold ecost. destruct (g <? ehi e); lia. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
