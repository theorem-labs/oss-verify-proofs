(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Notation d_tab := 0x255b18 (only parsing).
Notation d_nuniq := 0x655b18 (only parsing).
Notation d_map1 := 0x655b28 (only parsing).
Notation s_total := 0x245b08 (only parsing).
Notation s_data0 := 0x245b18 (only parsing).
Notation s_stored0 := 0x245b20 (only parsing).
Definition depotput_entry : Z := 0xa3628.
Definition put_entry : Z := 0xa3648.
Definition lock_entry : Z := 0xa3dbc.
Definition nstore_entry : Z := 0xa3340.
Definition sstore_entry : Z := 0xa102c.
Definition salloc_entry : Z := 0xa1150.

Definition mm_m : Z := 0xc6a4a7935bd1e995.
Definition mm_m8 : Z := 0x35253c9ade8f4ca8.
Definition mm_seed : Z := 0x9747b28c9747b28c.
Definition w64 (x : Z) : Z := x mod 2 ^ 64.
Definition mm_mix (k : Z) : Z := let k1 := w64 (k * mm_m) in w64 (Z.lxor (Z.shiftr k1 47) k1 * mm_m).
Definition mm_add (h k : Z) : Z := w64 (Z.lxor (mm_mix k) h * mm_m).
Definition mm_init (sz : Z) : Z := Z.lxor (w64 (sz * mm_m8)) mm_seed.
Definition mm_get (h : Z) : Z := let x := w64 (Z.lxor (Z.shiftr h 47) h * mm_m) in Z.lxor (Z.shiftr x 47) x.

Definition depot_hash (tr : list Z) : Z := mm_get (mm_add (fold_left mm_add tr (mm_init (Z.of_nat (length tr)))) 0).

Lemma mm_m8_ok : mm_m8 = w64 (8 * mm_m). Proof. reflexivity. Qed.

Lemma w64_range : forall x, 0 <= w64 x < 2 ^ 64.
Proof. intros x. unfold w64. apply Z.mod_pos_bound. lia. Qed.

Lemma lxor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. assert (P0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; lia). split; [exact P0|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NE]; [rewrite E; lia|].
  assert (P : 0 < Z.lxor a b) by lia.
  apply Z.log2_lt_pow2; [exact P|].
  pose proof (Z.log2_lxor a b (proj1 Ha) (proj1 Hb)) as L.
  destruct (Z.eq_dec a 0) as [->|Na]; destruct (Z.eq_dec b 0) as [->|Nb].
  - exfalso. apply NE. reflexivity.
  - rewrite Z.lxor_0_l. apply Z.log2_lt_pow2; lia.
  - rewrite Z.lxor_0_r. apply Z.log2_lt_pow2; lia.
  - pose proof (Z.log2_lt_pow2 a 64 ltac:(lia)) as La. pose proof (Z.log2_lt_pow2 b 64 ltac:(lia)) as Lb. lia.
Qed.

Lemma shiftr47_range : forall x, 0 <= x < 2 ^ 64 -> 0 <= Z.shiftr x 47 < 2 ^ 64.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma mm_add_range : forall h k, 0 <= mm_add h k < 2 ^ 64. Proof. intros. apply w64_range. Qed.
Lemma mm_init_range : forall sz, 0 <= mm_init sz < 2 ^ 64.
Proof. intros sz. unfold mm_init. apply lxor_range64; [apply w64_range| unfold mm_seed; lia]. Qed.
Lemma mm_get_range : forall h, 0 <= mm_get h < 2 ^ 64.
Proof.
  intros h. unfold mm_get. pose proof (w64_range (Z.lxor (Z.shiftr h 47) h * mm_m)) as R.
  apply lxor_range64; [apply shiftr47_range| ]; exact R.
Qed.
Lemma depot_hash_range : forall tr, 0 <= depot_hash tr < 2 ^ 64. Proof. intros. apply mm_get_range. Qed.

Record depot : Type := mkDepot { d_hs : list Z; d_tot : Z }.
Definition d_n (D : depot) : Z := Z.of_nat (length (d_hs D)).

Definition bkt (h : Z) : Z := h mod 2 ^ 20.
Definition hash_of (hs : list Z) (i : Z) : Z := nth (Z.to_nat (i - 1)) hs 0.

Fixpoint lastidx (p : Z -> bool) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: l' => let r := lastidx p l' in if r =? 0 then (if p x then 1 else 0) else r + 1
  end.

Definition tab_of (hs : list Z) (b : Z) : Z := lastidx (fun h => bkt h =? b) hs.
Definition link_of (hs : list Z) (i : Z) : Z := tab_of (firstn (Z.to_nat (i - 1)) hs) (bkt (hash_of hs i)).
Definition find_of (hs : list Z) (h : Z) : Z := lastidx (fun x => x =? h) hs.

Definition depot_put (D : depot) (tr : list Z) : depot * Z :=
  let h := depot_hash tr in
  let j := find_of (d_hs D) h in
  if j =? 0 then (mkDepot (d_hs D ++ [h]) (d_tot D + Z.of_nat (length tr) + 1), d_n D + 1) else (D, j).

Definition is_last (p : Z -> bool) (l : list Z) (j : Z) : Prop :=
  (j = 0 \/ (1 <= j <= Z.of_nat (length l) /\ p (nth (Z.to_nat (j - 1)) l 0) = true))
  /\ (forall k, j < k <= Z.of_nat (length l) -> p (nth (Z.to_nat (k - 1)) l 0) = false).

Lemma lastidx_snoc : forall p l x, lastidx p (l ++ [x]) = if p x then Z.of_nat (length l) + 1 else lastidx p l.
Proof.
  intros p l x. induction l as [|y l IH]; cbn [app lastidx length].
  - destruct (p x); reflexivity.
  - rewrite IH. destruct (p x) eqn:Px.
    + replace (Z.of_nat (length l) + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + reflexivity.
Qed.

Lemma lastidx_spec : forall p l, is_last p l (lastidx p l).
Proof.
  intros p l. induction l as [|x l IH] using rev_ind.
  - split; [left; reflexivity|]. intros k Hk. cbn in Hk. lia.
  - rewrite lastidx_snoc. unfold is_last in *. rewrite app_length. cbn [length]. destruct (p x) eqn:Px.
    + split; [right; split; [lia|]|].
      * replace (Z.to_nat (Z.of_nat (length l) + 1 - 1)) with (length l) by lia.
        rewrite app_nth2, Nat.sub_diag by lia. exact Px.
      * intros k Hk. lia.
    + destruct IH as [H1 H2]. split.
      * destruct H1 as [H1|(H1 & H1')]; [left; exact H1| right; split; [lia|]].
        rewrite app_nth1 by lia. exact H1'.
      * intros k Hk. destruct (Z.eq_dec k (Z.of_nat (length l) + 1)) as [->|Nk].
        -- replace (Z.to_nat (Z.of_nat (length l) + 1 - 1)) with (length l) by lia.
           rewrite app_nth2, Nat.sub_diag by lia. exact Px.
        -- rewrite app_nth1 by lia. apply H2. lia.
Qed.

Lemma is_last_unique : forall p l j1 j2, is_last p l j1 -> is_last p l j2 -> j1 = j2.
Proof.
  intros p l j1 j2 [A1 A2] [B1 B2].
  destruct (Z.lt_total j1 j2) as [L|[E|L]]; [| exact E|].
  - destruct B1 as [B1|(B1 & B1')]; [lia|]. rewrite A2 in B1' by lia. discriminate.
  - destruct A1 as [A1|(A1 & A1')]; [lia|]. rewrite B2 in A1' by lia. discriminate.
Qed.

Lemma lastidx_range : forall p l, 0 <= lastidx p l <= Z.of_nat (length l).
Proof. intros p l. destruct (lastidx_spec p l) as [[H|H] _]; lia. Qed.

Lemma nth_firstn_lt : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  intros l k i H. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
  - rewrite <- (firstn_skipn k l) at 2. rewrite app_nth1; [reflexivity|]. rewrite firstn_length. lia.
  - rewrite !nth_overflow; [reflexivity| exact L|]. rewrite firstn_length. lia.
Qed.

Definition walk_inv (hs : list Z) (h s : Z) : Prop :=
  exists k, 0 <= k <= Z.of_nat (length hs) /\ s = tab_of (firstn (Z.to_nat k) hs) (bkt h)
    /\ forall i, k < i <= Z.of_nat (length hs) -> hash_of hs i <> h.

Lemma walk_start : forall hs h, walk_inv hs h (tab_of hs (bkt h)).
Proof.
  intros hs h. exists (Z.of_nat (length hs)). split; [lia|]. split; [rewrite Nat2Z.id, firstn_all; reflexivity|].
  intros i Hi. lia.
Qed.

Lemma walk_range : forall hs h s, walk_inv hs h s -> 0 <= s <= Z.of_nat (length hs).
Proof.
  intros hs h s (k & Hk & -> & _). pose proof (lastidx_range (fun x => bkt x =? bkt h) (firstn (Z.to_nat k) hs)) as R.
  rewrite firstn_length in R. unfold tab_of. lia.
Qed.

Lemma walk_bucket : forall hs h s, walk_inv hs h s -> s <> 0 -> bkt (hash_of hs s) = bkt h.
Proof.
  intros hs h s (k & Hk & Es & _) Ns. destruct (lastidx_spec (fun x => bkt x =? bkt h) (firstn (Z.to_nat k) hs)) as [[A|(A1 & A2)] _];
    unfold tab_of in Es; [lia|]. rewrite <- Es in A1, A2. rewrite firstn_length in A1.
  rewrite nth_firstn_lt in A2 by lia. apply Z.eqb_eq in A2. exact A2.
Qed.

Lemma walk_zero : forall hs h, walk_inv hs h 0 -> find_of hs h = 0.
Proof.
  intros hs h (k & Hk & Es & HI). symmetry. apply (is_last_unique (fun x => x =? h) hs); [| apply lastidx_spec].
  split; [left; reflexivity|]. intros i Hi. apply Z.eqb_neq.
  destruct (Z.le_gt_cases i k) as [L|L]; [| apply HI; lia].
  destruct (lastidx_spec (fun x => bkt x =? bkt h) (firstn (Z.to_nat k) hs)) as [_ A]. unfold tab_of in Es. rewrite <- Es in A.
  rewrite firstn_length in A. specialize (A i ltac:(lia)). rewrite nth_firstn_lt in A by lia. apply Z.eqb_neq in A.
  intros E. apply A. unfold hash_of in E. rewrite E. reflexivity.
Qed.

Lemma walk_hit : forall hs h s, walk_inv hs h s -> s <> 0 -> hash_of hs s = h -> find_of hs h = s.
Proof.
  intros hs h s HW Ns Hh. pose proof (walk_range _ _ _ HW) as R. destruct HW as (k & Hk & Es & HI).
  symmetry. apply (is_last_unique (fun x => x =? h) hs); [| apply lastidx_spec].
  split; [right; split; [lia| apply Z.eqb_eq; exact Hh]|].
  intros i Hi. apply Z.eqb_neq.
  destruct (Z.le_gt_cases i k) as [L|L]; [| apply HI; lia].
  destruct (lastidx_spec (fun x => bkt x =? bkt h) (firstn (Z.to_nat k) hs)) as [_ A]. unfold tab_of in Es. rewrite <- Es in A.
  rewrite firstn_length in A. specialize (A i ltac:(lia)). rewrite nth_firstn_lt in A by lia. apply Z.eqb_neq in A.
  intros E. apply A. unfold hash_of in E. rewrite E. reflexivity.
Qed.

Lemma walk_next : forall hs h s, walk_inv hs h s -> s <> 0 -> hash_of hs s <> h ->
  walk_inv hs h (link_of hs s) /\ 0 <= link_of hs s < s.
Proof.
  intros hs h s HW Ns Hh. pose proof (walk_range _ _ _ HW) as R. pose proof (walk_bucket _ _ _ HW Ns) as Bk.
  destruct HW as (k & Hk & Es & HI).
  destruct (lastidx_spec (fun x => bkt x =? bkt h) (firstn (Z.to_nat k) hs)) as [[A|(A1 & A2)] A3];
    unfold tab_of in Es; [lia|]. rewrite <- Es in A1, A2, A3. rewrite firstn_length in A1, A3.
  unfold link_of. rewrite Bk. split.
  - exists (s - 1). split; [lia|]. split; [reflexivity|].
    intros i Hi. destruct (Z.eq_dec i s) as [->|Ni]; [exact Hh|].
    destruct (Z.le_gt_cases i k) as [L|L]; [| apply HI; lia].
    specialize (A3 i ltac:(lia)). rewrite nth_firstn_lt in A3 by lia. apply Z.eqb_neq in A3.
    intros E. apply A3. unfold hash_of in E. rewrite E. reflexivity.
  - pose proof (lastidx_range (fun x => bkt x =? bkt h) (firstn (Z.to_nat (s - 1)) hs)) as L.
    rewrite firstn_length in L. unfold tab_of. lia.
Qed.

Lemma tab_of_range : forall hs b, 0 <= tab_of hs b <= Z.of_nat (length hs).
Proof. intros. apply lastidx_range. Qed.

Lemma link_of_range : forall hs i, 1 <= i -> 0 <= link_of hs i < i.
Proof.
  intros hs i Hi. unfold link_of. pose proof (tab_of_range (firstn (Z.to_nat (i - 1)) hs) (bkt (hash_of hs i))) as R.
  rewrite firstn_length in R. lia.
Qed.

Lemma find_of_range : forall hs h, 0 <= find_of hs h <= Z.of_nat (length hs).
Proof. intros. apply lastidx_range. Qed.

Lemma find_of_hash : forall hs h, find_of hs h <> 0 -> hash_of hs (find_of hs h) = h.
Proof.
  intros hs h N. destruct (lastidx_spec (fun x => x =? h) hs) as [[A|(A1 & A2)] _]; unfold find_of in *; [lia|].
  apply Z.eqb_eq in A2. exact A2.
Qed.

Lemma find_of_zero_iff : forall hs h, find_of hs h = 0 <-> ~ In h hs.
Proof.
  intros hs h. destruct (lastidx_spec (fun x => x =? h) hs) as [A B]. unfold find_of. split.
  - intros E I. destruct (In_nth hs h 0 I) as (i & Hi & Ei).
    specialize (B (Z.of_nat i + 1) ltac:(lia)). replace (Z.to_nat (Z.of_nat i + 1 - 1)) with i in B by lia.
    rewrite Ei, Z.eqb_refl in B. discriminate.
  - intros NI. destruct A as [A|(A1 & A2)]; [exact A|]. exfalso. apply NI. apply Z.eqb_eq in A2. rewrite <- A2.
    apply nth_In. lia.
Qed.

Lemma tab_of_snoc : forall hs h b, tab_of (hs ++ [h]) b = if bkt h =? b then Z.of_nat (length hs) + 1 else tab_of hs b.
Proof. intros hs h b. unfold tab_of. exact (lastidx_snoc (fun x => bkt x =? b) hs h). Qed.

Lemma hash_of_snoc_old : forall hs h i, 1 <= i <= Z.of_nat (length hs) -> hash_of (hs ++ [h]) i = hash_of hs i.
Proof. intros hs h i Hi. unfold hash_of. rewrite app_nth1 by lia. reflexivity. Qed.

Lemma hash_of_snoc_new : forall hs h, hash_of (hs ++ [h]) (Z.of_nat (length hs) + 1) = h.
Proof.
  intros hs h. unfold hash_of. replace (Z.to_nat (Z.of_nat (length hs) + 1 - 1)) with (length hs) by lia.
  rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma link_of_snoc_old : forall hs h i, 1 <= i <= Z.of_nat (length hs) -> link_of (hs ++ [h]) i = link_of hs i.
Proof.
  intros hs h i Hi. unfold link_of. rewrite hash_of_snoc_old by exact Hi.
  rewrite firstn_app. replace (Z.to_nat (i - 1) - length hs)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma link_of_snoc_new : forall hs h, link_of (hs ++ [h]) (Z.of_nat (length hs) + 1) = tab_of hs (bkt h).
Proof.
  intros hs h. unfold link_of. rewrite hash_of_snoc_new.
  replace (Z.to_nat (Z.of_nat (length hs) + 1 - 1)) with (length hs) by lia.
  rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma depot_put_miss : forall D tr, find_of (d_hs D) (depot_hash tr) = 0 ->
  depot_put D tr = (mkDepot (d_hs D ++ [depot_hash tr]) (d_tot D + Z.of_nat (length tr) + 1), d_n D + 1).
Proof. intros D tr E. unfold depot_put. rewrite E. reflexivity. Qed.

Lemma depot_put_hit : forall D tr, find_of (d_hs D) (depot_hash tr) <> 0 ->
  depot_put D tr = (D, find_of (d_hs D) (depot_hash tr)).
Proof. intros D tr E. unfold depot_put. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. Qed.

Lemma depot_put_incl : forall D tr x, In x (d_hs (fst (depot_put D tr))) -> In x (d_hs D) \/ x = depot_hash tr.
Proof.
  intros D tr x H. unfold depot_put in H. destruct (find_of (d_hs D) (depot_hash tr) =? 0); cbn in H; [| left; exact H].
  apply in_app_or in H. destruct H as [H|[H|H]]; [left; exact H| right; symmetry; exact H| destruct H].
Qed.

Lemma depot_put_nodup : forall D tr, List.NoDup (d_hs D) -> List.NoDup (d_hs (fst (depot_put D tr))).
Proof.
  intros D tr ND. unfold depot_put. destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E]; cbn; [| exact ND].
  apply find_of_zero_iff in E. apply NoDup_app; [exact ND| constructor; [intros []| constructor]|].
  intros x H1 [H2|[]]. subst x. exact (E H1).
Qed.

Lemma depot_put_n : forall D tr, d_n (fst (depot_put D tr)) <= d_n D + 1.
Proof.
  intros D tr. unfold depot_put, d_n. destruct (find_of (d_hs D) (depot_hash tr) =? 0); cbn; [rewrite app_length; cbn; lia| lia].
Qed.

Lemma depot_put_tot : forall D tr, d_tot D <= d_tot (fst (depot_put D tr)) <= d_tot D + Z.of_nat (length tr) + 1.
Proof. intros D tr. unfold depot_put. destruct (find_of (d_hs D) (depot_hash tr) =? 0); cbn; lia. Qed.

Lemma depot_put_id : forall D tr, let (D', id) := depot_put D tr in
  1 <= id <= d_n D' /\ hash_of (d_hs D') id = depot_hash tr.
Proof.
  intros D tr. unfold depot_put. cbv zeta. destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E].
  - unfold d_n. cbn [d_hs]. rewrite app_length. cbn [length]. split; [lia|]. apply hash_of_snoc_new.
  - pose proof (find_of_range (d_hs D) (depot_hash tr)). split; [unfold d_n; lia|]. apply find_of_hash. exact E.
Qed.

Definition depot_rep (D : depot) (BK : list Z) (DNB SSB : Z) (m : mem) : Prop :=
  (forall b, In b BK -> 0 <= b < 2 ^ 20 /\ rw_cells asegs m (d_tab + 4 * b) [C4 (Z_to_bv 64 (tab_of (d_hs D) b))])
  /\ rw_cells asegs m d_nuniq [C4 (Z_to_bv 64 (d_n D))]
  /\ rw_cells asegs m d_map1 [C8 (Z_to_bv 64 DNB)]
  /\ (forall i, 1 <= i <= d_n D -> exists sid : word,
        rw_cells asegs m (DNB + 16 * i) [C8 (Z_to_bv 64 (hash_of (d_hs D) i)); C4 (Z_to_bv 64 (link_of (d_hs D) i)); C4 sid])
  /\ stk asegs m (DNB + 16 * (d_n D + 1)) (DNB + 2 ^ 20)
  /\ rw_cells asegs m s_total [C8 (Z_to_bv 64 (d_tot D))]
  /\ rw_cells asegs m s_data0 [C8 (Z_to_bv 64 SSB)]
  /\ rw_cells asegs m s_stored0 [C4 (Z_to_bv 64 (d_tot D))]
  /\ stk asegs m (SSB + 8 * d_tot D) (SSB + 2 ^ 23).

Definition depot_ok (D : depot) (DNB SSB lo : Z) : Prop :=
  Forall (fun h => 0 <= h < 2 ^ 64) (d_hs D)
  /\ d_n D + 1 < 2 ^ 16 /\ 0 <= d_tot D < 2 ^ 20
  /\ 0x6ca000 <= DNB /\ DNB + 2 ^ 20 <= lo
  /\ 0x6ca000 <= SSB /\ SSB + 2 ^ 23 <= lo
  /\ (DNB + 2 ^ 20 <= SSB \/ SSB + 2 ^ 23 <= DNB).

Definition depot_W (DNB SSB : Z) : list (Z * Z) :=
  [(d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8); (s_data0, s_stored0 + 4);
   (SSB, SSB + 2 ^ 23)].

Lemma dep_disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|].
  destruct H as [H3 H4]. split; [lia| eapply IH; eassumption].
Qed.

Lemma hash_of_range : forall hs i, Forall (fun h => 0 <= h < 2 ^ 64) hs -> 0 <= hash_of hs i < 2 ^ 64.
Proof.
  intros hs i HF. unfold hash_of. destruct (Nat.lt_ge_cases (Z.to_nat (i - 1)) (length hs)) as [L|L].
  - rewrite Forall_forall in HF. apply HF. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma depot_rep_frame : forall D BK DNB SSB lo W (m m' : mem), depot_rep D BK DNB SSB m -> depot_ok D DNB SSB lo ->
  munch W m m' -> wmono asegs m m' ->
  disjoint_from W d_tab (d_nuniq + 4 - d_tab) -> disjoint_from W d_map1 8 -> disjoint_from W DNB (2 ^ 20) ->
  disjoint_from W s_total 8 -> disjoint_from W s_data0 (s_stored0 + 4 - s_data0) -> disjoint_from W SSB (2 ^ 23) ->
  depot_rep D BK DNB SSB m'.
Proof.
  intros D BK DNB SSB lo W m m' (TB & NU & M1 & ND & FS & TT & DT & SD & FF) OK MU WM H1 H2 H3 H4 H5 H6.
  destruct OK as (HF & Hn & Ht & HD1 & HD2 & HS1 & HS2 & HDS).
  unfold d_n in *. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - intros b Hb. destruct (TB b Hb) as [Rb C]. split; [exact Rb|].
    apply (rw_cells_transport asegs W m m' _ _ C MU WM). cbn [cells_size csize Nat.add].
    eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ NU MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ M1 MU WM). exact H2.
  - intros i Hi. unfold d_n in Hi. destruct (ND i Hi) as (sid & C). exists sid. apply (rw_cells_transport asegs W m m' _ _ C MU WM).
    cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H3| |]; lia.
  - apply (stk_transport_disjoint asegs W m m' _ _ FS MU WM). eapply dep_disj_sub; [exact H3| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ TT MU WM). exact H4.
  - apply (rw_cells_transport asegs W m m' _ _ DT MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H5| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ SD MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H5| |]; lia.
  - apply (stk_transport_disjoint asegs W m m' _ _ FF MU WM). eapply dep_disj_sub; [exact H6| |]; lia.
Qed.

Lemma stk_carve_lo : forall (m : mem) lo hi (n : nat), stk asegs m lo hi -> lo + Z.of_nat n <= hi ->
  stk asegs m (lo + Z.of_nat n) hi /\ exists junk, rw_cells asegs m lo [CB n junk].
Proof.
  intros m lo hi n ST Hle. pose proof ST as (S1 & S2 & _).
  destruct (stk_split asegs m lo (lo + Z.of_nat n) hi ST ltac:(lia)) as [A B]. split; [exact B|].
  destruct (stk_carve asegs m lo (lo + Z.of_nat n) n A ltac:(lia)) as [_ (junk & C)]. exists junk.
  replace (lo + Z.of_nat n - Z.of_nat n) with lo in C by lia. exact C.
Qed.

Lemma dep_signed_lit : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63)%Z. lia.
Qed.

Ltac dIfT_s := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota| symmetry; unfold_cond; rewrite ?dep_signed_lit by lia; rewrite ?unsigned_lit by lia;
                                  solve_cond_rec] end.
Ltac dIfF_s := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; unfold_cond; rewrite ?dep_signed_lit by lia; rewrite ?unsigned_lit by lia;
                                   solve_cond_rec] end.

Ltac dIf_closed := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in change c with v; cbv iota end.

Lemma Z_to_le_bytes_app : forall n k z, 0 <= z ->
  Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z Hz; cbn [Nat.add Z_to_le_bytes app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). rewrite Z.shiftr_shiftr by lia.
    replace (8 + 8 * Z.of_nat n) with (8 * Z.of_nat (S n)) by lia. reflexivity.
Qed.

Lemma le8_split_small : forall v, 0 <= v < 2 ^ 32 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app by lia. f_equal. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. cbn. lia.
Qed.

Lemma rw_cells_c8_split : forall (m : mem) A pre post v, 0 <= v < 2 ^ 32 ->
  rw_cells asegs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> rw_cells asegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre post v Hv [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ W2]].
  split; [split|].
  - apply cells_wf_app. split; [exact W1| split; [exact I| split; [exact I| exact W2]]].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_split_small in B by exact Hv.
    rewrite <- app_assoc in B. exact B.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.

Lemma dep_bytes_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma dep_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (dep_bytes_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma dep_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (dep_bytes_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply dep_to_le_bytes_to_Z.
Qed.

Lemma dep_le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (dep_bytes_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply dep_to_le_bytes_to_Z.
Qed.

Lemma node_cells_of_cb : forall (m : mem) A bs, rw_cells asegs m A [CB 16 bs] ->
  rw_cells asegs m A [C8 (le_bytes_to_word (firstn 8 bs)); C4 (le_bytes_to_word (firstn 4 (skipn 8 bs)));
                      C4 (le_bytes_to_word (skipn 12 bs))].
Proof.
  intros m A bs [[W B] R]. cbn in W. destruct W as [W _].
  split; [split|].
  - cbn. repeat split.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *.
    rewrite dep_le8_of_bytes by (rewrite firstn_length; lia).
    rewrite dep_le4_of_bytes by (rewrite firstn_length, skipn_length; lia).
    rewrite dep_le4_of_bytes by (rewrite skipn_length; lia).
    replace (skipn 12 bs) with (skipn 4 (skipn 8 bs)) by (rewrite skipn_skipn; reflexivity).
    rewrite !firstn_skipn. exact B.
  - exact R.
Qed.

Lemma node_family_transport : forall W (m m' : mem) hs DNB n,
  (forall i, 1 <= i <= n -> exists sid : word,
     rw_cells asegs m (DNB + 16 * i) [C8 (Z_to_bv 64 (hash_of hs i)); C4 (Z_to_bv 64 (link_of hs i)); C4 sid]) ->
  munch W m m' -> wmono asegs m m' -> disjoint_from W DNB (2 ^ 20) -> n + 1 <= 2 ^ 16 ->
  forall i, 1 <= i <= n -> exists sid : word,
     rw_cells asegs m' (DNB + 16 * i) [C8 (Z_to_bv 64 (hash_of hs i)); C4 (Z_to_bv 64 (link_of hs i)); C4 sid].
Proof.
  intros W m m' hs DNB n ND MU WM HD Hn i Hi. destruct (ND i Hi) as (sid & C). exists sid.
  apply (rw_cells_transport asegs W m m' _ _ C MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
Qed.
