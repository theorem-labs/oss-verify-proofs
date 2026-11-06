From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table memset_c bcmp_c memcpy_c reac_rival_kind_of_c reac_arbitrate_c.
Import ListNotations.
Open Scope Z_scope.

Lemma zle_ble : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (ble_range bs) as R. pose proof (bv_unsigned_in_range 8 b) as Rb.
  unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  rewrite lor_shiftl8_add by lia.
  replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

Lemma le4_mod32 : forall v w : word, bv_unsigned v mod 2^32 = bv_unsigned w mod 2^32 -> le4 v = le4 w.
Proof.
  intros v w H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32) by lia.
  rewrite H. reflexivity.
Qed.

Lemma le2_mod16 : forall v w : word, bv_unsigned v mod 2^16 = bv_unsigned w mod 2^16 -> le2 v = le2 w.
Proof.
  intros v w H. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned v) 16), <- (Z_to_le_bytes_mod 2 (bv_unsigned w) 16) by lia.
  rewrite H. reflexivity.
Qed.

Lemma le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. apply le4_mod32. unfold sx32. rewrite unsigned_lit_wrap.
  pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  mlia.
Qed.

Lemma le2_sx16 : forall v : word, le2 (sx16 v) = le2 v.
Proof.
  intros v. apply le2_mod16. unfold sx16. rewrite unsigned_lit_wrap.
  pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with (2^15). change (bv_modulus 16) with (2^16).
  mlia.
Qed.

Lemma ble_le4 : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  unfold le4. rewrite unsigned_lit by lia. rewrite <- L. apply zle_ble.
Qed.

Lemma ble_le4s : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))) = bs.
Proof.
  intros bs L. transitivity (le4 (Z_to_bv 64 (bytes_le_to_Z bs))); [|apply ble_le4; exact L].
  apply le4_mod32. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  mlia.
Qed.

Lemma ble_le2 : forall bs, length bs = 2%nat -> le2 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  unfold le2. rewrite unsigned_lit by lia. rewrite <- L. apply zle_ble.
Qed.

Lemma ble_le8 : forall bs, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. rewrite <- L. apply zle_ble.
Qed.

Lemma ble_b1 : forall bs, length bs = 1%nat -> [Z_to_bv 8 (bytes_le_to_Z bs)] = bs.
Proof.
  intros bs L. pose proof (zle_ble bs) as H. rewrite L in H. cbn [Z_to_le_bytes] in H. exact H.
Qed.

Lemma bytes_eqb_true : forall l r, bytes_eqb l r = true <-> l = r.
Proof.
  induction l as [|x l IH]; intros [|y r]; cbn; try (split; congruence).
  rewrite andb_true_iff, Z.eqb_eq, IH. split.
  - intros [E1 E2]. subst r. f_equal. apply bv_eq. exact E1.
  - intros E. inversion E. subst. split; reflexivity.
Qed.

Section Scan.
Variable c : Z -> bool.
Variable g : Z -> Z.

Definition stp (b : option Z) (i : Z) : option Z :=
  if c i then match b with None => Some i | Some q => if g q <? g i then Some i else b end else b.

Definition mx (b : Z) (l : list Z) : Z := fold_right (fun i acc => Z.max (g i) acc) b l.

Definition bestl (l : list Z) : option Z :=
  match List.filter c l with
  | [] => None
  | j :: _ => List.find (fun i => g i =? mx (g j) (List.filter c l)) (List.filter c l)
  end.

Lemma find_app : forall (f : Z -> bool) l1 l2,
  List.find f (l1 ++ l2) = match List.find f l1 with Some x => Some x | None => List.find f l2 end.
Proof. intros f l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. destruct (f x); [reflexivity|exact IH]. Qed.

Lemma find_none_intro : forall (f : Z -> bool) l, (forall y, In y l -> f y = false) -> List.find f l = None.
Proof.
  intros f l. induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma mx_app1 : forall b l x, mx b (l ++ [x]) = Z.max (mx b l) (g x).
Proof.
  intros b l x. unfold mx. induction l as [|y l IH]; cbn [fold_right app]; [lia|]. rewrite IH. lia.
Qed.

Lemma mx_ge : forall b l y, In y l -> g y <= mx b l.
Proof.
  intros b l y. unfold mx. induction l as [|x l IH]; cbn [fold_right In]; [tauto|].
  intros [->|H]; [lia|]. specialize (IH H). lia.
Qed.

Lemma mx_att : forall b l, mx b l = b \/ exists y, In y l /\ g y = mx b l.
Proof.
  intros b l. unfold mx. induction l as [|x l IH]; cbn [fold_right In]; [left; reflexivity|].
  destruct (Z.le_gt_cases (fold_right (fun i acc => Z.max (g i) acc) b l) (g x)) as [H|H].
  - right. exists x. split; [left; reflexivity|lia].
  - rewrite Z.max_r by lia. destruct IH as [IH|(y & Hy & Hg)]; [left; exact IH|].
    right. exists y. split; [right; exact Hy|exact Hg].
Qed.

Lemma find_attain : forall j r,
  exists q, List.find (fun i => g i =? mx (g j) (j :: r)) (j :: r) = Some q /\ g q = mx (g j) (j :: r).
Proof.
  intros j r. destruct (List.find (fun i => g i =? mx (g j) (j :: r)) (j :: r)) as [q|] eqn:E.
  - apply List.find_some in E. destruct E as [_ E]. apply Z.eqb_eq in E. exists q. split; [reflexivity|exact E].
  - exfalso. destruct (mx_att (g j) (j :: r)) as [H|(y & Hy & Hg)].
    + pose proof (List.find_none _ _ E j (or_introl eq_refl)) as N. cbv beta in N. rewrite H, Z.eqb_refl in N.
      discriminate.
    + pose proof (List.find_none _ _ E y Hy) as N. cbv beta in N. rewrite Hg, Z.eqb_refl in N. discriminate.
Qed.

Lemma scan_best : forall l, fold_left stp l None = bestl l.
Proof.
  intros l. induction l as [|x l IH] using rev_ind; [reflexivity|].
  rewrite fold_left_app. cbn [fold_left]. rewrite IH. unfold bestl.
  rewrite filter_app. cbn [List.filter].
  unfold stp. destruct (c x) eqn:Cx.
  - destruct (List.filter c l) as [|j r].
    + cbn [app List.find]. unfold mx. cbn [fold_right]. rewrite Z.max_id, Z.eqb_refl. reflexivity.
    + destruct (find_attain j r) as (q & Hq & Gq). cbv beta iota. rewrite Hq. cbn [app].
      change (j :: r ++ [x]) with ((j :: r) ++ [x]). rewrite mx_app1, find_app.
      destruct (Z.ltb_spec (g q) (g x)) as [L|L].
      * rewrite Z.max_r by lia. rewrite find_none_intro.
        -- cbn [List.find]. rewrite Z.eqb_refl. reflexivity.
        -- intros y Hy. apply Z.eqb_neq. pose proof (mx_ge (g j) (j :: r) y Hy). lia.
      * rewrite Z.max_l by lia. rewrite Hq. reflexivity.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma fold_in : forall l b j, fold_left stp l b = Some j -> b = Some j \/ In j l.
Proof.
  induction l as [|x l IH]; intros b j H; cbn in H; [left; exact H|].
  destruct (IH _ _ H) as [H1|H1]; [|right; right; exact H1].
  unfold stp in H1. destruct (c x); [|left; exact H1].
  destruct b as [q|]; [destruct (g q <? g x)|]; inversion H1; subst; first [left; reflexivity | right; left; reflexivity].
Qed.

End Scan.

Definition scanz (T P : list byte) (our now i : Z) : option Z :=
  fold_left (stp (cand T P our now) (last_of T)) (map Z.of_nat (seq 0 (Z.to_nat i))) None.

Lemma scanz_succ : forall T P our now i, 0 <= i ->
  scanz T P our now (i + 1) = stp (cand T P our now) (last_of T) (scanz T P our now i) i.
Proof.
  intros T P our now i Hi. unfold scanz. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  rewrite seq_app, map_app, fold_left_app. cbn [seq map fold_left Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma scanz_range : forall T P our now i j, scanz T P our now i = Some j -> 0 <= j < i.
Proof.
  intros T P our now i j H. unfold scanz in H. apply fold_in in H. destruct H as [H|H]; [discriminate|].
  apply in_map_iff in H. destruct H as (x & <- & Hx). apply in_seq in Hx. lia.
Qed.

Lemma best_scanz : forall t T P our now, t <> 0 -> best t T P our now = scanz T P our now (n_of T).
Proof.
  intros t T P our now Ht. unfold best, scanz. rewrite (proj2 (Z.eqb_neq t 0) Ht).
  rewrite scan_best. reflexivity.
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = 2 * (x / 2).
Proof.
  intros x Hx. change 18446744073709551614 with (2 * Z.ones 63).
  assert (Hq : 0 <= x / 2 < 2^63) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Ni].
  - rewrite !Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_even_succ by lia.
    rewrite (Z.div_mod x 2) at 1 by lia.
    assert (M : x mod 2 = 0 \/ x mod 2 = 1) by (pose proof (Z.mod_pos_bound x 2); lia).
    destruct M as [M|M]; rewrite M; [rewrite Z.add_0_r, Z.testbit_even_succ by lia | rewrite Z.testbit_odd_succ by lia];
      (destruct (Z.ltb_spec (i - 1) 63) as [L|L];
       [rewrite Z.ones_spec_low by lia; apply andb_true_r
       | rewrite Z.ones_spec_high by lia; rewrite andb_false_r; symmetry; apply (testbit_high_false _ 63); lia]).
Qed.

Lemma est_eq : forall fsm, -2^31 <= fsm < 2^31 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614)) (Z_to_bv 64 2) =
  (fsm =? 2) || (fsm =? 3).
Proof.
  intros fsm Hf. rewrite unsigned_lit_wrap. rewrite land_m2 by (apply Z.mod_pos_bound; lia).
  unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec fsm 2) as [->|N2]; [reflexivity|].
  destruct (Z.eqb_spec fsm 3) as [->|N3]; [reflexivity|].
  cbn [orb]. apply Z.eqb_neq. mlia.
Qed.

Lemma prob_eq : forall fsm, -2^31 <= fsm < 2^31 -> bv_eqb (Z_to_bv 64 fsm) (Z_to_bv 64 1) = (fsm =? 1).
Proof.
  intros fsm Hf. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec fsm 1) as [->|N]; [reflexivity|]. apply Z.eqb_neq. mlia.
Qed.

Lemma stk_keep : forall m m' lo hi a n bs,
  stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' -> bytes_at rsegs m' a bs ->
  Z.of_nat (length bs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n bs (H1 & H2 & H) MU WM (B1 & B2 & B) L.
  split; [lia|]. split; [lia|]. intros x Hx. destruct (H x Hx) as [W [b Hb]].
  split; [apply WM, W|].
  destruct (Z.le_gt_cases a x) as [Ha|Ha]; [destruct (Z.lt_ge_cases x (a + n)) as [Hn|Hn]|].
  - pose proof (B (Z.to_nat (x - a)) ltac:(lia)) as Bx. replace (a + Z.of_nat (Z.to_nat (x - a))) with x in Bx by lia.
    destruct (nth_error bs (Z.to_nat (x - a))) as [b'|] eqn:E; [exists b'; exact Bx|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hn & H)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
  - intros [[[W1 B1] (Ha & Hn & H1)] [[W2 B2] (Ha2 & Hn2 & H2)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply H2. lia.
Qed.

Definition baddr (t : Z) (bo : option Z) : Z := match bo with None => 0 | Some j => t + 48 * j end.

Lemma sx32_lit : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma u_range : forall T k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length T) -> 0 <= u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof. intros T k n Hk H. unfold u_at. pose proof (ble_range (sub T k n)) as R. rewrite length_sub in R by lia. exact R. Qed.

Lemma sub_s32 : forall T k, 0 <= k -> k + 4 <= Z.of_nat (length T) -> sub T k 4 = le4 (Z_to_bv 64 (s32_at T k)).
Proof. intros T k Hk H. unfold s32_at, u_at. symmetry. apply ble_le4s. apply length_sub; lia. Qed.

Lemma sub_u32 : forall T k, 0 <= k -> k + 4 <= Z.of_nat (length T) -> sub T k 4 = le4 (Z_to_bv 64 (u_at T k 4)).
Proof. intros T k Hk H. unfold u_at. symmetry. apply ble_le4. apply length_sub; lia. Qed.

Lemma sub_u16 : forall T k, 0 <= k -> k + 2 <= Z.of_nat (length T) -> sub T k 2 = le2 (Z_to_bv 64 (u_at T k 2)).
Proof. intros T k Hk H. unfold u_at. symmetry. apply ble_le2. apply length_sub; lia. Qed.

Lemma sub_u64 : forall T k, 0 <= k -> k + 8 <= Z.of_nat (length T) -> sub T k 8 = le8 (Z_to_bv 64 (u_at T k 8)).
Proof. intros T k Hk H. unfold u_at. symmetry. apply ble_le8. apply length_sub; lia. Qed.

Lemma sub_u8 : forall T k, 0 <= k -> k + 1 <= Z.of_nat (length T) -> sub T k 1 = [Z_to_bv 8 (u_at T k 1)].
Proof. intros T k Hk H. unfold u_at. symmetry. apply ble_b1. apply length_sub; lia. Qed.

Lemma firstn_add' : forall {X} n1 n2 (l : list X), firstn (n1 + n2) l = firstn n1 l ++ firstn n2 (skipn n1 l).
Proof.
  intros X n1. induction n1 as [|n1 IH]; intros n2 l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. f_equal. apply IH.
Qed.

Lemma sub_split : forall bs k n1 n2, 0 <= k -> sub bs k (n1 + n2) = sub bs k n1 ++ sub bs (k + Z.of_nat n1) n2.
Proof.
  intros bs k n1 n2 Hk. unfold sub. rewrite firstn_add', skipn_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bytes_at_sub' : forall m a bs k n a', bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  a' = a + k -> bytes_at rsegs m a' (sub bs k n).
Proof. intros m a bs k n a' H Hk Hn ->. apply bytes_at_sub; assumption. Qed.

Lemma rd_sub' : forall m a bs k n a' r, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  a' = a + k -> sub bs k n = r -> ov_read_bytes rsegs m (Z_to_bv 64 a') n = Some r.
Proof. intros m a bs k n a' r H Hk Hn -> <-. apply rd_sub; assumption. Qed.

Lemma mul48 : forall n, 0 <= n <= 8 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 6)) - bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 4))
  = 48 * n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2^6) with 64. change (2^4) with 16. rewrite !unsigned_lit by lia. lia.
Qed.

Ltac rdf H BT LT T k n lem :=
  pose proof (rd_sub' _ _ _ k n _ _ BT ltac:(lia) ltac:(rewrite LT; lia) eq_refl (lem T k ltac:(lia) ltac:(rewrite LT; lia))) as H.

Ltac zc HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; zify_bool HC; Z.div_mod_to_equations; lia.

Ltac rk_some RK BT LT T t j :=
  let Rd := fresh "Rd" in let Rs := fresh "Rs" in let Rc := fresh "Rc" in let Rr := fresh "Rr" in
  pose proof (u_range T (48 * j + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rd;
  pose proof (u_range T (48 * j + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rs;
  pose proof (u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as Rc;
  change (2 ^ (8 * Z.of_nat 1)) with (2^8) in Rd, Rs; change (2 ^ (8 * Z.of_nat 4)) with (2^32) in Rc;
  pose proof (s32_range T (48 * j + 8)) as Rr;
  eapply evt_cut;
  [ eapply RK with (e := t + 48 * j) (r := role_of_e T j) (d := hd_of T j) (s := slots_of T j) (c := ch_of T j);
    [ reflexivity | lia | mlia
    | intros _; split; [exact Rr|]; split; [exact Rd|]; split; [exact Rs|]; split; [exact Rc|];
      split; [|split; [|split]];
      [ eapply bytes_at_ext; [apply (bytes_at_sub' _ t T (48 * j + 8) 4); [exact BT | lia | rewrite LT; lia | lia]|];
        apply sub_s32; [lia | rewrite LT; lia]
      | eapply bytes_at_ext; [apply (bytes_at_sub' _ t T (48 * j + 12) 1); [exact BT | lia | rewrite LT; lia | lia]|];
        apply sub_u8; [lia | rewrite LT; lia]
      | eapply bytes_at_ext; [apply (bytes_at_sub' _ t T (48 * j + 16) 1); [exact BT | lia | rewrite LT; lia | lia]|];
        apply sub_u8; [lia | rewrite LT; lia]
      | eapply bytes_at_ext; [apply (bytes_at_sub' _ t T (48 * j + 20) 4); [exact BT | lia | rewrite LT; lia | lia]|];
        apply sub_u32; [lia | rewrite LT; lia] ] ]
  | ];
  let ms' := fresh "ms'" in let E := fresh "E" in
  intros ms' (? & ? & ? & ? & ? & E); subst ms';
  rewrite (proj2 (Z.eqb_neq (t + 48 * j) 0)) by lia; cbv iota;
  fold (rival_of T j).

Ltac mcpy_tail MC PP LP EPI out our :=
  do 4 step;
  lazymatch goal with OCh : rw_cells _ ?mm out ?cs |- _ => split_for_access OCh rsegs mm out cs 4%nat 6%nat end;
  let OCa := fresh "OCa" in let OCr := fresh "OCr" in let OCb := fresh "OCb" in let OCz := fresh "OCz" in
  lazymatch goal with OCh : rw_cells _ ?mm out (?c0 :: ?c1 :: ?rest) |- _ =>
    apply (proj1 (rw_cells_app mm out [c0] (c1 :: rest))) in OCh; destruct OCh as [OCa OCr];
    apply (proj1 (rw_cells_app mm _ [c1] rest)) in OCr; destruct OCr as [OCb OCz]
  end;
  cbn [cells_size csize Nat.add] in OCb, OCz;
  replace (out + Z.of_nat 4) with (out + 4) in OCb, OCz by lia;
  replace (out + 4 + Z.of_nat 6) with (out + 10) in OCz by lia;
  let E6 := fresh "E6" in let Eo4 := fresh "Eo4" in let Eour := fresh "Eour" in
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity;
  assert (Eo4 : bv_unsigned (Z_to_bv 64 (out + 4)) = out + 4) by (apply unsigned_lit; lia);
  assert (Eour : bv_unsigned (Z_to_bv 64 our) = our) by (apply unsigned_lit; lia);
  lazymatch type of OCb with rw_cells _ ?mm (out + 4) [CB 6 ?jk] =>
    eapply evt_cut;
    [ eapply MC with (junk := jk);
      [ rewrite Eour; apply PP; assumption
      | rewrite E6; exact LP
      | rewrite Eo4, E6; exact OCb
      | rewrite Eo4, Eour, E6; lia
      | assumption ]
    | ]
  end;
  let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
  let OCn := fresh "OCn" in let SRC := fresh "SRC" in let m4 := fresh "m" in
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & E & MUc & WMc & MIc & OCn & SRC);
  subst ms'; rewrite Eo4, E6 in MUc, OCn; rewrite Eour in SRC; change (Z.to_nat 6) with 6%nat in OCn;
  let LS := fresh "LS" in let STn := fresh "STn" in
  lazymatch type of OCn with rw_cells _ _ _ [CB 6 ?src] =>
    assert (LS : Z.of_nat (length (cells_bytes [CB 6 src])) = 6) by (cbn [cells_bytes cbytes]; rewrite length_app, LP; reflexivity)
  end;
  lazymatch type of MUc with munch _ ?mo ?mn =>
    lazymatch goal with STh : stk _ mo ?lo _ |- _ =>
      pose proof (stk_keep _ _ _ _ (out + 4) 6 _ STh MUc WMc (proj2 (proj1 OCn)) LS) as STn
    end;
    transport_after_call rsegs mo mn MUc WMc
  end;
  clear MUc WMc LS;
  let OCm := fresh "OCm" in
  lazymatch type of OCn with rw_cells _ ?mm _ [CB 6 ?src] =>
  lazymatch type of OCa with rw_cells _ mm out [?c0] =>
  lazymatch type of OCz with rw_cells _ mm (out + 10) ?rest =>
    assert (OCm : rw_cells rsegs mm out (c0 :: CB 6 src :: rest));
    [ apply (proj2 (rw_cells_app mm out [c0] (CB 6 src :: rest))); split; [exact OCa|];
      cbn [cells_size csize Nat.add]; replace (out + Z.of_nat 4) with (out + 4) by lia;
      apply (proj2 (rw_cells_app mm (out + 4) [CB 6 src] rest)); split; [exact OCn|];
      cbn [cells_size csize Nat.add]; replace (out + 4 + Z.of_nat 6) with (out + 10) by lia; exact OCz
    | clear OCa OCz OCn ]
  end end end;
  rewrite (ret_pc_even 0x16448) by (cbn; lia);
  step; step; step;
  eapply EPI; try eassumption;
  lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.

Theorem reac_arbitrate_holds :
  memset_contract -> bcmp_contract -> memcpy_contract -> reac_rival_kind_of_contract -> reac_arbitrate_contract.
Proof.
  intros MSC BC MC RK. unfold reac_arbitrate_contract, REAC_ARBITRATE, REAC_ARBITRATE_K.
  unfold MEMSET in MSC. unfold BCMP in BC. unfold REAC_RIVAL_KIND_OF in RK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    t our fsm pace now out lo T P O -> -> -> -> -> -> Ht Hour Hfsm Hpace Hnow Hout Hsp16 ST LO HT HP Ho4 LO32 HO WO DO MI.
  unfold off_window in DO, HT, HP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound rsegs m out O HO) as OB. rewrite LO32 in OB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 96%nat ST.
  do 22 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (OC : rw_cells rsegs m1 out [CB 32 O]).
  { split; [split; [cbn; split; [exact LO32|exact I] | cbn; rewrite app_nil_r; exact HO] | cbn; exact WO]. }
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
  assert (Eout : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MSC with (junk := O); [rewrite Eout, E32; exact OC | exact MI]. }
  intros ms' PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & E & MUc & WMc & MIc & OCc).
  subst ms'. rewrite Eout, E32 in MUc, OCc.
  change (rw_cells rsegs m2 out [CB 32 (repeat (Z_to_bv 8 0) 32)]) in OCc.
  pose proof (stk_keep _ _ _ _ out 32 _ ST MUc WMc (proj2 (proj1 OCc)) eq_refl) as ST2.
  transport_after_call rsegs m1 m2 MUc WMc.
  clear MUc WMc MI E32 Eout.
  rewrite (ret_pc_even 0x16334) by (cbn; lia).
  step. step. step.
  clear m1.
  assert (TT : forall mm, munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m mm -> t <> 0 ->
                          bytes_at rsegs mm t T).
  { intros mm MUm Ht0. destruct (HT Ht0) as (_ & LT & BT & _ & DT & DTo).
    eapply bytes_at_transport; [exact BT | exact MUm | rewrite LT; cbn [disjoint_from]; repeat split; try exact I; lia]. }
  assert (PP : forall mm, munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m mm -> our <> 0 ->
                          bytes_at rsegs mm our P).
  { intros mm MUm Hu0. destruct (HP Hu0) as (LP & BP & DP & DPo).
    eapply bytes_at_transport; [exact BP | exact MUm | rewrite LP; cbn [disjoint_from]; repeat split; try exact I; lia]. }
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs |- _ =>
  assert (EPI : forall (m2 : word -> option byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                                                     x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -96) fcs -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    bytes_at rsegs m2 out (arb_model t our T P fsm pace now) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x16464) fc None m2 (seg_rom rsegs)))
  end.
  { intros m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
      FR2 ST3 MU2 WM2 MI2 OB2.
    do 11 step. release_frame FR2 ST3 (bv_unsigned sp). do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST3|]. split; [exact OB2|].
    split; [intros Ht0; apply TT; assumption | intros Hu0; apply PP; assumption]. }
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs, OCh : rw_cells _ _ out ?ocs |- _ =>
  assert (AFTER : forall (m2 : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25
                                                       x28 x29 x30 x31 : word),
    x18 = Z_to_bv 64 (baddr t (best t T P our now)) ->
    rw_cells rsegs m2 (bv_unsigned sp + -96) fcs -> rw_cells rsegs m2 out ocs -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 our)
                          x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 fsm) (Z_to_bv 64 now) x21
                          (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614)) x23 x24 x25
                          s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x163bc) fc None m2 (seg_rom rsegs)))
  end.
  { intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x28 x29 x30 x31 E18 FR2 OC2 ST3 MU2 WM2 MI2.
    subst x18. clear FR OCc ST2 MU WM MIc WO.
    destruct ((fsm =? 2) || (fsm =? 3)) eqn:EST.
    - destruct (best t T P our now) as [j|] eqn:Hb; cbn [baddr].
      + assert (Ht0 : t <> 0) by (intro E0; unfold best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
        pose proof Hb as Hb0. rewrite best_scanz in Hb0 by exact Ht0. pose proof (scanz_range _ _ _ _ _ _ Hb0) as Rj.
        destruct (HT Ht0) as (Ht8 & LT & _ & (T1 & _ & _ & _) & DT & DTo). unfold tbl_T1 in T1.
        pose proof (TT _ MU2 Ht0) as BT2. pose proof (bytes_at_bound rsegs _ t T BT2) as TB. rewrite LT in TB.
        step. step. rewrite est_eq by exact Hfsm. rewrite EST. cbn [negb].
        step. step.
        replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (t + 48 * j))) with (Z_to_bv 64 1)
          by (rewrite v_sltu_b2z, !unsigned_lit by lia; rewrite (proj2 (Z.ltb_lt 0 (t + 48 * j))) by lia; reflexivity).
        do 4 step.
        rk_some RK BT2 LT T t j.
        rewrite (ret_pc_even 0x163dc) by (cbn; lia).
        step. step. if_cases HC; [exfalso; zc HC|].
        rdf RC BT2 LT T (48 * j + 20) 4%nat sub_u32.
        step. step. step. step.
        rewrite eqb_lit by lia. destruct (Z.eqb_spec our 0) as [Hu0|Hu0]; cbv iota.
        { eapply EPI; try eassumption.
          lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.
          unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_eq our 0) Hu0). cbv zeta iota.
          unfold arb_bytes, z4, MAC0. cbn [cells_bytes cbytes app repeat firstn skipn]. rewrite ?le4_sx32. reflexivity. }
        destruct (HP Hu0) as (LP & _ & DP & DPo).
        mcpy_tail MC PP LP EPI out our.
        unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_neq our 0) Hu0). cbv zeta iota.
        unfold arb_bytes, z4. cbn [cells_bytes cbytes app repeat firstn skipn]. rewrite ?le4_sx32. reflexivity.
      + step. step. rewrite est_eq by exact Hfsm. rewrite EST. cbn [negb].
        step. step.
        replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (rewrite v_sltu_b2z; reflexivity).
        do 4 step.
        eapply evt_cut.
        { eapply RK with (e := 0) (r := 0) (d := 0) (s := 0) (c := 0);
            [reflexivity | lia | reflexivity | intros H0; exfalso; apply H0; reflexivity]. }
        intros ms' (z11 & z12 & z13 & z14 & z15 & E). subst ms'.
        rewrite (ret_pc_even 0x163dc) by (cbn; lia).
        try change (if 0 =? 0 then 0 else reac_rival_kind_model 0 0 0 0) with 0.
        step. step. if_cases HC; [|exfalso; zc HC].
        step. step. step.
        rewrite eqb_lit by lia. destruct (Z.eqb_spec our 0) as [Hu0|Hu0]; cbv iota.
        { eapply EPI; try eassumption.
          lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.
          unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_eq our 0) Hu0). cbv zeta iota.
          unfold arb_bytes, z4, MAC0. cbn [cells_bytes cbytes app repeat firstn skipn]. reflexivity. }
        destruct (HP Hu0) as (LP & _ & DP & DPo).
        mcpy_tail MC PP LP EPI out our.
        unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_neq our 0) Hu0). cbv zeta iota.
        unfold arb_bytes, z4. cbn [cells_bytes cbytes app repeat firstn skipn]. reflexivity.
    - destruct (best t T P our now) as [j|] eqn:Hb; cbn [baddr].
      + assert (Ht0 : t <> 0) by (intro E0; unfold best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
        pose proof Hb as Hb0. rewrite best_scanz in Hb0 by exact Ht0. pose proof (scanz_range _ _ _ _ _ _ Hb0) as Rj.
        destruct (HT Ht0) as (Ht8 & LT & _ & (T1 & _ & _ & _) & DT & DTo). unfold tbl_T1 in T1.
        pose proof (TT _ MU2 Ht0) as BT2. pose proof (bytes_at_bound rsegs _ t T BT2) as TB. rewrite LT in TB.
        step. step. rewrite est_eq by exact Hfsm. rewrite EST. cbn [negb].
        step. if_cases HC; [exfalso; zc HC|].
        step. step.
        rdf RM4 BT2 LT T (48 * j) 4%nat sub_u32.
        step. step. clear RM4.
        rdf RM2 BT2 LT T (48 * j + 4) 2%nat sub_u16.
        step. clear RM2.
        do 5 step.
        rk_some RK BT2 LT T t j.
        rewrite (ret_pc_even 0x16418) by (cbn; lia).
        rdf RC BT2 LT T (48 * j + 20) 4%nat sub_u32.
        do 5 step.
        eapply EPI; try eassumption.
        lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.
        unfold arb_model. rewrite Hb, EST. cbv zeta iota.
        unfold arb_bytes, z4, mac_of. cbn [cells_bytes cbytes app repeat firstn skipn].
        rewrite ?le4_sx32, ?le2_sx16.
        rewrite <- (sub_u32 T (48 * j)) by (rewrite ?LT; lia).
        rewrite <- (sub_u16 T (48 * j + 4)) by (rewrite ?LT; lia).
        change (sub T (48 * j) 6) with (sub T (48 * j) (4 + 2)). rewrite sub_split by lia.
        replace (48 * j + Z.of_nat 4) with (48 * j + 4) by lia.
        rewrite <- app_assoc. reflexivity.
      + step. step. rewrite est_eq by exact Hfsm. rewrite EST. cbn [negb].
        step. if_cases HC; [|exfalso; zc HC].
        step. step. rewrite prob_eq by exact Hfsm.
        destruct (Z.eqb_spec fsm 1) as [F1|F1]; cbn [negb].
        * step. step. rewrite eqb_lit by lia. destruct (Z.eqb_spec our 0) as [Hu0|Hu0]; cbn [negb].
          -- eapply EPI; try eassumption.
             lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.
             unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_eq fsm 1) F1), (proj2 (Z.eqb_eq our 0) Hu0). cbv zeta iota.
             unfold arb_bytes, z4, MAC0. cbn [cells_bytes cbytes app repeat firstn skipn]. reflexivity.
          -- destruct (HP Hu0) as (LP & _ & DP & DPo).
             mcpy_tail MC PP LP EPI out our.
             unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_eq fsm 1) F1), (proj2 (Z.eqb_neq our 0) Hu0). cbv zeta iota.
             unfold arb_bytes, z4. cbn [cells_bytes cbytes app repeat firstn skipn]. reflexivity.
        * eapply EPI; try eassumption.
          lazymatch goal with OCh : rw_cells _ _ out _ |- _ => eapply bytes_at_ext; [exact (proj2 (proj1 OCh))|] end.
          unfold arb_model. rewrite Hb, EST, (proj2 (Z.eqb_neq fsm 1) F1). cbv zeta iota.
          unfold arb_bytes, z4, MAC0. cbn [cells_bytes cbytes app repeat firstn skipn]. reflexivity. }
  rewrite eqb_lit by lia. destruct (Z.eqb_spec t 0) as [Ht0|Ht0]; cbv iota.
  { step. eapply AFTER; try eassumption. unfold best. rewrite (proj2 (Z.eqb_eq t 0) Ht0). reflexivity. }
  destruct (HT Ht0) as (Ht8 & LT & _ & TOK & DT & DTo).
  pose proof (TT _ MU Ht0) as BT.
  pose proof (bytes_at_bound rsegs _ t T BT) as TB. rewrite LT in TB.
  destruct TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof (rd_sub _ t T 384 4 BT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step. rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  set (n := n_of T) in *. assert (En : n = n_of T) by reflexivity. clearbody n.
  step. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 n) as [Hn|Hn]; cbn [negb].
  2: { step. eapply AFTER; try eassumption. rewrite best_scanz by exact Ht0. unfold scanz.
       rewrite <- En. replace (Z.to_nat n) with 0%nat by lia. reflexivity. }
  clear RN. do 9 step.
  rewrite mul48 by lia.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs, OCh : rw_cells _ _ out ?ocs |- _ =>
  assert (LOOP : forall k i (m2 : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    rw_cells rsegs m2 (bv_unsigned sp + -96) fcs -> rw_cells rsegs m2 out ocs -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 our)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (baddr t (scanz T P our now i)))
                          (Z_to_bv 64 fsm) (Z_to_bv 64 now) (Z_to_bv 64 (t + 48 * i))
                          (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614))
                          (Z_to_bv 64 2) (Z_to_bv 64 (t + 48 * n)) (Z_to_bv 64 5000000000) s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x1636c) fc None m2 (seg_rom rsegs)))
  end.
  { induction k as [|k IH];
      intros i m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi FR2 OC2 ST3 MU2 WM2 MI2; [lia|].
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs, OCh : rw_cells _ _ out ?ocs |- _ =>
    assert (TL : forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
      y18 = Z_to_bv 64 (baddr t (scanz T P our now (i + 1))) ->
      rw_cells rsegs m3 (bv_unsigned sp + -96) fcs -> rw_cells rsegs m3 out ocs -> stk rsegs m3 lo (bv_unsigned sp + -96) ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 our)
                            y10 y11 y12 y13 y14 y15 y16 y17 y18
                            (Z_to_bv 64 fsm) (Z_to_bv 64 now) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614))
                            (Z_to_bv 64 2) (Z_to_bv 64 (t + 48 * n)) (Z_to_bv 64 5000000000) s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x163ac) fc None m3 (seg_rom rsegs)))
    end.
    { intros m3 u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u18 u28 u29 u30 u31 E18 FR3 OC3 ST4 MU3 WM3 MI3. subst u18.
      step. step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (t + 48 * i + 48) (t + 48 * n)) as [E1|E1]; cbn [negb].
      - step. eapply AFTER; try eassumption. rewrite best_scanz by exact Ht0. rewrite <- En.
        replace n with (i + 1) by lia. reflexivity.
      - replace (t + 48 * i + 48) with (t + 48 * (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; lia. }
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs, OCh : rw_cells _ _ out ?ocs |- _ =>
    assert (NST : forall (m3 : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      cand T P our now i = true ->
      rw_cells rsegs m3 (bv_unsigned sp + -96) fcs -> rw_cells rsegs m3 out ocs -> stk rsegs m3 lo (bv_unsigned sp + -96) ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 our)
                            (Z_to_bv 64 (last_of T i)) y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 (baddr t (scanz T P our now i)))
                            (Z_to_bv 64 fsm) (Z_to_bv 64 now) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614))
                            (Z_to_bv 64 2) (Z_to_bv 64 (t + 48 * n)) (Z_to_bv 64 5000000000) s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x1639c) fc None m3 (seg_rom rsegs)))
    end.
    { intros m3 u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 CI FR3 OC3 ST4 MU3 WM3 MI3.
      pose proof (TT _ MU3 Ht0) as BT3.
      pose proof (u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as Ri8.
      change (u_at T (48 * i + 40) 8) with (last_of T i) in Ri8. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in Ri8.
      destruct (scanz T P our now i) as [q|] eqn:Hq; cbn [baddr].
      - pose proof (scanz_range _ _ _ _ _ _ Hq) as Rq.
        step. if_cases HC; [exfalso; zc HC|].
        assert (RLq : ov_read_bytes rsegs m3 (Z_to_bv 64 (t + 48 * q + 40)) 8 = Some (le8 (Z_to_bv 64 (last_of T q)))).
        { apply (rd_sub' _ t T (48 * q + 40) 8); [exact BT3 | lia | rewrite LT; lia | lia | apply sub_u64; [lia | rewrite LT; lia]]. }
        pose proof (u_range T (48 * q + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as Rq8.
        change (u_at T (48 * q + 40) 8) with (last_of T q) in Rq8. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in Rq8.
        step. step. rewrite ltu_lit by lia.
        destruct (Z.ltb_spec (last_of T q) (last_of T i)) as [L|L]; cbn [negb].
        + step. eapply TL; try eassumption. rewrite scanz_succ by lia. rewrite Hq. unfold stp. rewrite CI.
          rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
        + eapply TL; try eassumption. rewrite scanz_succ by lia. rewrite Hq. unfold stp. rewrite CI.
          rewrite (proj2 (Z.ltb_ge _ _) L). reflexivity.
      - step. if_cases HC; [|exfalso; zc HC].
        step. eapply TL; try eassumption. rewrite scanz_succ by lia. rewrite Hq. unfold stp. rewrite CI. reflexivity. }
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -96) ?fcs, OCh : rw_cells _ _ out ?ocs |- _ =>
    assert (STL : forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ((our =? 0) || negb (bytes_eqb (mac_of T i) P)) = true ->
      rw_cells rsegs m3 (bv_unsigned sp + -96) fcs -> rw_cells rsegs m3 out ocs -> stk rsegs m3 lo (bv_unsigned sp + -96) ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 32)] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 ->
      role_of_e T i = 2 ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 our)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 (baddr t (scanz T P our now i)))
                            (Z_to_bv 64 fsm) (Z_to_bv 64 now) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fsm)) 18446744073709551614))
                            (Z_to_bv 64 2) (Z_to_bv 64 (t + 48 * n)) (Z_to_bv 64 5000000000) s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x1638c) fc None m3 (seg_rom rsegs)))
    end.
    { intros m3 u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 CO FR3 OC3 ST4 MU3 WM3 MI3 R2.
      pose proof (TT _ MU3 Ht0) as BT3.
      assert (RL : ov_read_bytes rsegs m3 (Z_to_bv 64 (t + 48 * i + 40)) 8 = Some (le8 (Z_to_bv 64 (last_of T i)))).
      { apply (rd_sub' _ t T (48 * i + 40) 8); [exact BT3 | lia | rewrite LT; lia | lia | apply sub_u64; [lia | rewrite LT; lia]]. }
      pose proof (u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as Ri8.
      change (u_at T (48 * i + 40) 8) with (last_of T i) in Ri8. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in Ri8.
      step. step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (last_of T i) now) as [L|L]; cbn [negb].
      - step. rewrite (unsigned_lit now), (unsigned_lit (last_of T i)) by lia.
        step. rewrite ltu_lit by lia.
        destruct (Z.ltb_spec 5000000000 (now - last_of T i)) as [S|S]; cbv iota.
        + eapply TL; try eassumption. rewrite scanz_succ by lia. unfold stp.
          replace (cand T P our now i) with false; [reflexivity|].
          unfold cand, stale. rewrite R2, CO. replace REAC_DISCO_STALE_NS with 5000000000 by reflexivity.
          rewrite (proj2 (Z.ltb_lt _ _) L), (proj2 (Z.ltb_lt _ _) S). reflexivity.
        + eapply NST; try eassumption.
          unfold cand, stale. rewrite R2, CO. replace REAC_DISCO_STALE_NS with 5000000000 by reflexivity.
          rewrite (proj2 (Z.ltb_lt _ _) L), (proj2 (Z.ltb_ge _ _) S). reflexivity.
      - eapply NST; try eassumption.
        unfold cand, stale. rewrite R2, CO. rewrite (proj2 (Z.ltb_ge _ _) L). reflexivity. }
    pose proof (TT _ MU2 Ht0) as BT2.
    pose proof (s32_range T (48 * i + 8)) as Rr. change (s32_at T (48 * i + 8)) with (role_of_e T i) in Rr.
    assert (RR : ov_read_bytes rsegs m2 (Z_to_bv 64 (t + 48 * i + 8)) 4 = Some (le4 (Z_to_bv 64 (role_of_e T i)))).
    { apply (rd_sub' _ t T (48 * i + 8) 4); [exact BT2 | lia | rewrite LT; lia | lia | apply sub_s32; [lia | rewrite LT; lia]]. }
    step. rewrite sx32_lit by exact Rr.
    step.
    if_cases HC.
    { assert (R2 : role_of_e T i <> 2) by zc HC. clear HC.
      eapply TL; try eassumption. rewrite scanz_succ by lia. unfold stp.
      unfold cand. rewrite (proj2 (Z.eqb_neq _ 2) R2). reflexivity. }
    assert (R2 : role_of_e T i = 2) by zc HC. clear HC RR.
    assert (ML : length (mac_of T i) = 6%nat) by (unfold mac_of; apply length_sub; rewrite ?LT; lia).
    step.
    rewrite eqb_lit by lia. destruct (Z.eqb_spec our 0) as [Hu0|Hu0]; cbv iota.
    { eapply STL; try eassumption. reflexivity. }
    destruct (HP Hu0) as (LP & _ & DP & DPo).
    do 4 step.
    destruct (memcmp6 (mac_of T i) P ML LP) as (v & Hv & Veq & Vr).
    eapply evt_cut.
    { eapply BC with (ls := mac_of T i) (rs := P) (v := v).
      - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact BT2 | lia | rewrite LT; lia].
      - rewrite unsigned_lit by lia. apply PP; assumption.
      - exact Hv.
      - exact MI2. }
    post_call rsegs m2.
    step. rewrite eqb_small by exact Vr.
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
    + eapply TL; try eassumption. rewrite scanz_succ by lia. unfold stp.
      replace (cand T P our now i) with false; [reflexivity|].
      unfold cand. rewrite R2, (proj2 (Z.eqb_neq our 0) Hu0), (proj2 (bytes_eqb_true _ _) (proj1 Veq V0)). reflexivity.
    + eapply STL; try eassumption. try rewrite (proj2 (Z.eqb_neq our 0) Hu0). cbn [orb].
      destruct (bytes_eqb (mac_of T i) P) eqn:BE; [|reflexivity]. exfalso. apply V0. apply Veq. apply bytes_eqb_true. exact BE. }
  replace (Z_to_bv 64 t) with (Z_to_bv 64 (t + 48 * 0)) by (f_equal; lia).
  eapply (LOOP (Z.to_nat n) 0); try eassumption; lia.
Qed.
