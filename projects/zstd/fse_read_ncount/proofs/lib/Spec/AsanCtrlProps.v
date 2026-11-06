(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint zseq (lo : Z) (n : nat) : list Z :=
match n with O => [] | S m => lo :: zseq (lo + 1) m end.
Lemma zseq_spec : forall n lo x, In x (zseq lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
induction n; intros; simpl.
- split; [intros []|lia].
- rewrite Nat2Z.inj_succ. rewrite IHn. lia.
Qed.
Lemma forallb_zseq : forall (p : Z -> bool) lo n,
forallb p (zseq lo n) = true -> forall x, lo <= x < lo + Z.of_nat n -> p x = true.
Proof.
intros p lo n H x Hx. rewrite forallb_forall in H. apply H. apply zseq_spec. exact Hx.
Qed.
Definition prim_ok (n : Z) : bool :=
let c := class_id (needed_size n) in
(0 <=? rz_log n) && (rz_log n <=? 7) && (rz_size n =? 16 * 2 ^ rz_log n)
&& Bool.eqb (is_primary n) (n <=? 64512)
&& (if is_primary n then (1 <=? c) && (c <=? 30) && (needed_size n <=? size_of_class c) && (32 <=? size_of_class c)
&& (size_of_class c <=? 65536) && (2 <=? max_cached c) && (max_cached c <=? 16)
&& (max_cached c / 2 * size_of_class c <=? K_USER_MAP) && (Z.even (max_cached c))
else (needed_size n =? rup (Z.max n 8) 8 + 2 * 2048)).
Lemma prim_ok_range : forallb prim_ok (zseq 0 (Z.to_nat 70000)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma prim_facts : forall n, 0 <= n < 70000 -> prim_ok n = true.
Proof. intros. apply (forallb_zseq prim_ok 0 (Z.to_nat 70000) prim_ok_range). rewrite Z2Nat.id; lia. Qed.
Lemma is_primary_iff : forall n, 0 <= n < 70000 -> is_primary n = (n <=? 64512).
Proof.
intros n H. pose proof (prim_facts n H) as P. unfold prim_ok in P. cbn zeta in P.
repeat rewrite Bool.andb_true_iff in P.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
match goal with Hb : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in Hb; exact Hb end.
Qed.
Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
Lemma rup8_ge : forall m, 0 <= m -> m <= rup m 8.
Proof.
intros m Hm. unfold rup.
pose proof (Z.div_mod (m + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m + 8 - 1) 8 ltac:(lia)). lia.
Qed.
Lemma large_not_primary : forall n, 64512 < n -> is_primary n = false.
Proof.
intros n H. unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_gt.
assert (Hr : rz_log n = 7).
{ unfold rz_log.
rewrite (proj2 (Z.leb_gt n 48)) by lia. rewrite (proj2 (Z.leb_gt n 96)) by lia.
rewrite (proj2 (Z.leb_gt n 448)) by lia. rewrite (proj2 (Z.leb_gt n 3968)) by lia.
rewrite (proj2 (Z.leb_gt n 16128)) by lia. rewrite (proj2 (Z.leb_gt n 32256)) by lia.
rewrite (proj2 (Z.leb_gt n 64512)) by lia. reflexivity. }
unfold rz_size. rewrite Hr. change (Z.shiftl 16 7) with 2048.
unfold rounded_size. pose proof (rup8_ge (Z.max n 8) ltac:(lia)). lia.
Qed.
Lemma primary_class_facts : forall n, 0 <= n -> is_primary n = true ->
let c := class_id (needed_size n) in
1 <= c <= 30 /\ needed_size n <= size_of_class c /\ 32 <= size_of_class c <= 65536
/\ 2 <= max_cached c <= 16 /\ max_cached c / 2 * size_of_class c <= K_USER_MAP /\ Z.even (max_cached c) = true.
Proof.
intros n Hn Hp.
assert (n < 70000) by (destruct (Z_lt_dec n 70000); auto; rewrite large_not_primary in Hp; [discriminate|lia]).
pose proof (prim_facts n ltac:(lia)) as P. unfold prim_ok in P. cbn zeta in P. rewrite Hp in P.
repeat rewrite Bool.andb_true_iff in P.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
cbn zeta. repeat split; auto; lia.
Qed.
Lemma poison0_small : forall R (a s : Z) (k : AM R), a mod 8 = 0 -> 0 <= s < 524288 -> poison0 a s k = k.
Proof.
intros R a s k Ha Hs. unfold poison0.
destruct (s =? 0) eqn:E0; [reflexivity|].
replace (SHADOW_OFF + Z.shiftr (a + s - 8) 3 + 1 - (SHADOW_OFF + Z.shiftr a 3) <? CLEAR_SHADOW_MMAP_THRESHOLD) with true; [reflexivity|].
symmetry. apply Z.ltb_lt. unfold CLEAR_SHADOW_MMAP_THRESHOLD.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
pose proof (Z.div_mod (a + s - 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + s - 8) 8 ltac:(lia)). lia.
Qed.
Fixpoint tdepth {E A R} (t : stree E A R) (n : nat) {struct t} : Prop :=
match t with
| SRet _ => True
| SVis _ k => match n with O => False | S m => forall a, tdepth (k a) m end
end.
Lemma tdepth_ret : forall E A R (r : R) n, @tdepth E A R (SRet r) n.
Proof. intros; simpl; auto. Qed.
Lemma aundef_depth : forall R w (k : AM R) n, tdepth k n -> tdepth (aundef_ w k) (S n).
Proof. intros. unfold aundef_. simpl. auto. Qed.
Ltac peel :=
lazymatch goal with
| |- True => exact I
| |- forall _, _ => intros ?
| |- tdepth (SRet _) _ => apply tdepth_ret
| |- tdepth (aundef_ _ _) (S _) => apply aundef_depth
| |- tdepth (aundef_ _ _) ?m => destruct m; [exfalso|apply aundef_depth]
| |- tdepth (SVis _ _) (S _) => simpl; intros ?
| |- tdepth (ev _ _) (S _) => unfold ev at 1; simpl; intros ?
| |- tdepth (if ?b then _ else _) _ => destruct b
| |- tdepth (match ?x with _ => _ end) _ => destruct x
end.
Lemma rup_small : forall x a, 0 < a -> 0 < x <= a -> rup x a = a.
Proof.
intros x a Ha Hx. unfold rup.
assert (E : (x + a - 1) / a = 1) by (symmetry; apply Z.div_unique with (r := x - 1); lia).
rewrite E. lia.
Qed.
Section Totality.
Variable AV : list (Z * Z).
Variable ATOP : Z.
Hypothesis HATOP : ALLOC_TOP_MIN <= ATOP <= 2^47.
#[using="Type"] Lemma fixed_answer_ok_self : forall a, fixed_answer_ok a a = true.
Proof. intros. unfold fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r. Qed.
#[using="Type"] Lemma carve_enough_nomap : forall mapped alloc size req,
0 < size -> 0 <= alloc -> 0 <= req -> alloc + req * size <= mapped -> (mapped - alloc) / size >= req.
Proof. intros. apply Z.le_ge. apply Z.div_le_lower_bound; [lia|nia]. Qed.
#[using="Type"] Lemma get_put_eq : forall st c r, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_put_ne : forall st c c' r, c <> c' -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_ne; auto. Qed.
#[using="Type"] Lemma max_count_put : forall st c r c', max_count (put_cls c r st) c' = max_count st c'.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros. unfold init_cache, max_count. destruct (a_cinit st) eqn:E; [rewrite E|]; reflexivity. Qed.
#[using="Type"] Lemma rup_ge : forall x a, 0 < a -> x <= rup x a.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.
#[using="Type"] Lemma rup_le : forall x a, 0 < a -> rup x a <= x + a - 1.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.
#[using="Type"] Lemma rup_freearr_bounds : forall x, 0 <= x -> 0 <= rup x K_FREEARR_MAP <= x + K_FREEARR_MAP.
Proof.
intros. unfold rup, K_FREEARR_MAP.
pose proof (Z.div_mod (x + 262144 - 1) 262144 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 262144 - 1) 262144 ltac:(lia)).
pose proof (Z.div_pos (x + 262144 - 1) 262144 ltac:(lia) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma carve_facts : forall x size, 0 < size -> 0 <= x ->
0 <= x / size /\ 0 <= x / size * size <= x /\ x - x / size * size < size.
Proof.
intros x size Hs Hx. pose proof (Z.div_pos x size Hx Hs).
rewrite (Z.mul_comm (x / size) size). pose proof (Z.div_mod x size ltac:(lia)). pose proof (Z.mod_pos_bound x size ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma sec_map_size_bounds : forall n, 64512 < n <= 2^40 -> n + 4096 <= sec_map_size n <= n + 4096 + 4096 + 4096 + 8.
Proof.
intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
assert (Hr : rz_size n = 2048).
{ unfold rz_size, rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. }
rewrite Hr. pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). pose proof (rup_le (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)).
unfold PG in *. lia.
Qed.
End Totality.
