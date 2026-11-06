(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List Bool.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition round_up (x a : Z) : Z := (x + a - 1) / a * a.
Definition round_down (x a : Z) : Z := x / a * a.

Lemma round_up_ge : forall x a, 0 < a -> x <= round_up x a.
Proof. intros x a Ha. unfold round_up. pose proof (Z_div_mod_eq_full (x + a - 1) a). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). lia. Qed.
Lemma round_up_lt : forall x a, 0 < a -> round_up x a < x + a.
Proof. intros x a Ha. unfold round_up. pose proof (Z_div_mod_eq_full (x + a - 1) a). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). lia. Qed.
Lemma round_up_mod : forall x a, 0 < a -> round_up x a mod a = 0.
Proof. intros x a Ha. unfold round_up. apply Z_mod_mult. Qed.
Lemma round_up_id : forall x a, 0 < a -> x mod a = 0 -> round_up x a = x.
Proof.
  intros x a Ha Hm. unfold round_up.
  pose proof (Z_div_mod_eq_full x a) as E. rewrite Hm, Z.add_0_r in E.
  replace (x + a - 1) with ((a - 1) + (x / a) * a) by lia.
  rewrite Z_div_plus_full, Z.div_small by lia. lia.
Qed.
Lemma round_up_mono : forall x y a, 0 < a -> x <= y -> round_up x a <= round_up y a.
Proof. intros x y a Ha Hxy. unfold round_up. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma round_down_le : forall x a, 0 < a -> round_down x a <= x.
Proof. intros x a Ha. unfold round_down. pose proof (Z_div_mod_eq_full x a). pose proof (Z.mod_pos_bound x a Ha). lia. Qed.
Lemma round_down_gt : forall x a, 0 < a -> x - a < round_down x a.
Proof. intros x a Ha. unfold round_down. pose proof (Z_div_mod_eq_full x a). pose proof (Z.mod_pos_bound x a Ha). lia. Qed.
Lemma round_down_mod : forall x a, 0 < a -> round_down x a mod a = 0.
Proof. intros x a Ha. unfold round_down. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma mod0_down : forall a b c, (c | b) -> a mod b = 0 -> a mod c = 0.
Proof. intros a b c Hd H. rewrite <- (Z.mod_mod_divide a b c Hd), H. reflexivity. Qed.
Lemma divide_wit : forall c k, (c | c * k). Proof. intros. exists k. lia. Qed.

(* [comment removed for export] *)
Fixpoint zforall (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && zforall f (lo + 1) n' end.
Lemma zforall_spec : forall f n lo, zforall f lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  induction n as [|n IH]; intros lo H x Hx; cbn in H; [lia|].
  apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1)); [exact H2|lia].
Qed.
(* [comment removed for export] *)
Definition zall (lo hi : Z) (f : Z -> bool) : bool := zforall f lo (Z.to_nat (hi - lo + 1)).
Lemma zall_spec : forall lo hi f, zall lo hi f = true -> forall x, lo <= x <= hi -> f x = true.
Proof. intros lo hi f H x Hx. unfold zall in H. eapply zforall_spec; [exact H|]. rewrite Z2Nat.id; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2 ^ rz_log n.      (* [comment removed for export] *)

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (Z.leb _ _)); lia. Qed.
Lemma rz_size_eq : forall n, rz_size n = Z.shiftl 16 (rz_log n).
Proof. intros. rewrite Z.shiftl_mul_pow2 by (pose proof (rz_log_range n); lia). reflexivity. Qed.
Lemma rz_size_cases : forall n,
  rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/
  rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (Z.leb _ _)); cbn; lia. Qed.
Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048.
Proof. intros n. pose proof (rz_size_cases n). lia. Qed.
Lemma rz_size_mod16 : forall n, rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. Qed.
(* [comment removed for export] *)
Lemma rz_log_small : forall n, n <= 64512 -> rz_log n <= 6.
Proof. intros n H. unfold rz_log. repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end; lia. Qed.
Lemma rz_log_large : forall n, 64512 < n -> rz_log n = 7.
Proof. intros n H. unfold rz_log. repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end; lia. Qed.
Lemma rz_size_large : forall n, 64512 < n -> rz_size n = 2048.
Proof. intros n H. unfold rz_size. rewrite rz_log_large by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition user_size (n : Z) : Z := if n =? 0 then 1 else n.
(* [comment removed for export] *)
Definition rounded_size (n : Z) : Z := round_up (Z.max n 8) 8.
Definition needed_size (n : Z) : Z := rounded_size n + rz_size n.
(* [comment removed for export] *)
Definition from_primary (n : Z) : bool := needed_size n <=? kMaxSize.
(* [comment removed for export] *)
Definition needed_size2 (n : Z) : Z := if from_primary n then needed_size n else needed_size n + rz_size n.
(* [comment removed for export] *)
Definition map_size (n : Z) : Z := round_up (needed_size2 n) kPageSize + kPageSize.

Lemma user_size_pos : forall n, 0 <= n -> 1 <= user_size n /\ n <= user_size n /\ (0 < n -> user_size n = n).
Proof. intros n H. unfold user_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma rounded_size_ge : forall n, n <= rounded_size n /\ 8 <= rounded_size n.
Proof. intros n. unfold rounded_size. pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)). lia. Qed.
Lemma rounded_size_lt : forall n, rounded_size n < Z.max n 8 + 8.
Proof. intros n. unfold rounded_size. apply round_up_lt. lia. Qed.
Lemma rounded_size_mod8 : forall n, rounded_size n mod 8 = 0.
Proof. intros. unfold rounded_size. apply round_up_mod. lia. Qed.
(* [comment removed for export] *)
Lemma rounded_user_size : forall n, 0 <= n -> user_size n <= rounded_size n.
Proof. intros n H. unfold user_size. pose proof (rounded_size_ge n). destruct (Z.eqb_spec n 0); lia. Qed.
Lemma needed_size_mod8 : forall n, needed_size n mod 8 = 0.
Proof.
  intros n. unfold needed_size. rewrite Z.add_mod by lia. rewrite rounded_size_mod8.
  rewrite (mod0_down (rz_size n) 16 8 (divide_wit 8 2) (rz_size_mod16 n)). reflexivity.
Qed.
Lemma needed_size_ge : forall n, n + 16 <= needed_size n /\ 24 <= needed_size n.
Proof. intros n. unfold needed_size. pose proof (rounded_size_ge n). pose proof (rz_size_range n). lia. Qed.

(* [comment removed for export] *)
Lemma from_primary_iff : forall n, from_primary n = true <-> n <= kMaxPrimaryUser.
Proof.
  intros n. unfold from_primary, needed_size, kMaxSize, kMaxPrimaryUser. rewrite Z.leb_le.
  pose proof (rounded_size_ge n) as G. pose proof (rounded_size_lt n) as L.
  split; intros H.
  - destruct (Z.le_gt_cases n 64512) as [|C]; [assumption|]. rewrite rz_size_large in H by lia. lia.
  - unfold rz_size. pose proof (rz_log_range n) as R.
    destruct (Z.le_gt_cases n 32256) as [A|A].
    + assert (E : rz_log n <= 5). { unfold rz_log. repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end; lia. }
      assert (2 ^ rz_log n <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia). change (2^5) with 32 in *. lia.
    + assert (E : rz_log n = 6). { unfold rz_log. repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end; lia. }
      rewrite E. change (2^6) with 64. unfold rounded_size in *.
      pose proof (round_up_mono (Z.max n 8) 64512 8 ltac:(lia) ltac:(lia)). change (round_up 64512 8) with 64512 in *. lia.
Qed.
Lemma from_primary_false_iff : forall n, from_primary n = false <-> kMaxPrimaryUser < n.
Proof.
  intros n. pose proof (from_primary_iff n) as [A B]. destruct (from_primary n); split; intros H; try discriminate; try reflexivity.
  - exfalso. specialize (A eq_refl). lia.
  - destruct (Z.le_gt_cases n kMaxPrimaryUser) as [LE|GT]; [|exact GT]. exfalso. specialize (B LE). discriminate.
Qed.
Lemma needed_size_primary_le : forall n, from_primary n = true -> needed_size n <= kMaxSize.
Proof. intros n H. unfold from_primary in H. apply Z.leb_le in H. exact H. Qed.
(* [comment removed for export] *)
Lemma needed_size2_secondary : forall n, kMaxPrimaryUser < n -> needed_size2 n = rounded_size n + 4096.
Proof. intros n H. unfold needed_size2. pose proof (proj2 (from_primary_false_iff n) H) as F. rewrite F.
  unfold needed_size. rewrite rz_size_large by (unfold kMaxPrimaryUser in H; lia). lia. Qed.
Lemma needed_size2_mod8 : forall n, needed_size2 n mod 8 = 0.
Proof. intros n. unfold needed_size2. destruct (from_primary n); [apply needed_size_mod8|].
  rewrite Z.add_mod, needed_size_mod8 by lia. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. Qed.
Lemma map_size_page : forall n, map_size n mod kPageSize = 0.
Proof. intros. unfold map_size. rewrite Z.add_mod, round_up_mod, Z_mod_same_full by (unfold kPageSize; lia). reflexivity. Qed.
Lemma map_size_room : forall n, needed_size2 n + kPageSize <= map_size n < needed_size2 n + 2 * kPageSize.
Proof. intros. unfold map_size. pose proof (round_up_ge (needed_size2 n) kPageSize ltac:(unfold kPageSize; lia)).
  pose proof (round_up_lt (needed_size2 n) kPageSize ltac:(unfold kPageSize; lia)). lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition class_size (c : Z) : Z :=
  if c =? kBatchClassID then 64
  else if c <=? kMidClass then kMinSize * c
  else let c' := c - kMidClass in
       let t := Z.shiftl kMidSize (Z.shiftr c' 1) in
       t + Z.shiftr t 1 * Z.land c' 1.

(* [comment removed for export] *)
Definition size_class (s : Z) : Z :=
  if kMaxSize <? s then 0
  else if s <=? kMidSize then Z.shiftr (s + kMinSize - 1) 5
  else let l := Z.log2 s in
       let hbits := Z.land (Z.shiftr s (l - 1)) 1 in
       let lbits := Z.land s (Z.ones (l - 1)) in
       kMidClass + Z.shiftl (l - 9) 1 + hbits + (if lbits =? 0 then 0 else 1).

(* [comment removed for export] *)
Definition class_of (n : Z) : Z := size_class (needed_size n).

(* [comment removed for export] *)
Definition max_cached_hint (size : Z) : Z := if size =? 0 then 0 else Z.max 1 (Z.min kMaxNumCachedHint (1024 / size)).
Definition max_cached (c : Z) : Z := max_cached_hint (class_size c).
Definition max_count (c : Z) : Z := 2 * max_cached c.
(* [comment removed for export] *)
Definition refill_count (c : Z) : Z := max_cached c.

(* [comment removed for export] *)
Definition carve_count (mapped_user allocated_user size : Z) : Z := (mapped_user - allocated_user) / size.
(* [comment removed for export] *)
Definition user_map_growth (mapped_user allocated_user size k : Z) : Z :=
  let total := allocated_user + k * size in
  if total <=? mapped_user then 0 else round_up (total - mapped_user) kUserMapSize.
(* [comment removed for export] *)
Definition free_array_need (nfreed : Z) : Z := round_up (4 * nfreed) kFreeArrayMapSize.

(* [comment removed for export] *)
Definition class_size_tab : list Z :=
  [32;64;96;128;160;192;224;256;288;320;352;384;416;448;480;512;
   768;1024;1536;2048;3072;4096;6144;8192;12288;16384;24576;32768;49152;65536].
Definition max_count_tab : list Z :=
  [16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4; 2;2;2;2;2;2;2;2;2;2;2;2;2;2].
Definition fresh_carve_tab : list Z :=
  [8192;4096;2730;2048;1638;1365;1170;1024;910;819;744;682;630;585;546;512;
   341;256;170;128;85;64;42;32;21;16;10;8;5;4].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma class_size_24 : class_size kQuarantineBatchClass = kQuarantineBatchBytes. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma max_count_31 : max_count 31 = 16. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma class_size_range : forall c, 1 <= c <= 30 -> 32 <= class_size c <= kMaxSize.
Proof.
  intros c Hc. assert (E : zall 1 30 (fun c => (32 <=? class_size c) && (class_size c <=? kMaxSize)) = true) by (vm_compute; reflexivity).
  pose proof (zall_spec _ _ _ E c Hc) as H. cbv beta in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma class_size_mod32 : forall c, 1 <= c <= 30 -> class_size c mod 32 = 0.
Proof.
  intros c Hc. assert (E : zall 1 30 (fun c => class_size c mod 32 =? 0) = true) by (vm_compute; reflexivity).
  pose proof (zall_spec _ _ _ E c Hc) as H. cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.
(* [comment removed for export] *)
Lemma max_count_range : forall c, 1 <= c <= 30 -> 2 <= max_count c <= 16 /\ max_count c = 2 * refill_count c /\ 1 <= refill_count c <= 8.
Proof.
  intros c Hc. assert (E : zall 1 30 (fun c => (2 <=? max_count c) && (max_count c <=? 16) && (1 <=? refill_count c) && (refill_count c <=? 8)) = true) by (vm_compute; reflexivity).
  pose proof (zall_spec _ _ _ E c Hc) as H. cbv beta in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with K : (_ <=? _) = true |- _ => apply Z.leb_le in K end.
  unfold max_count, refill_count in *. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma size_class_small : forall s, 1 <= s <= 512 -> size_class s = (s + 31) / 32.
Proof. intros s Hs. unfold size_class, kMaxSize, kMidSize, kMinSize. destruct (Z.ltb_spec 0x10000 s); [lia|].
  destruct (Z.leb_spec s 512); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma size_class_ok : forall s, 1 <= s <= kMaxSize ->
  1 <= size_class s <= 30 /\ s <= class_size (size_class s) /\ (size_class s = 1 \/ class_size (size_class s - 1) < s).
Proof.
  intros s Hs.
  assert (E : zall 1 kMaxSize (fun s => let c := size_class s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && ((c =? 1) || (class_size (c - 1) <? s))) = true) by (vm_compute; reflexivity).
  pose proof (zall_spec _ _ _ E s Hs) as H. cbv beta in H. cbv zeta in H.
  apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C.
  split; [lia|]. split; [exact C|].
  apply orb_prop in D as [D|D]; [left; apply Z.eqb_eq in D; exact D | right; apply Z.ltb_lt in D; exact D].
Qed.
Lemma size_class_range : forall s, 1 <= s <= kMaxSize -> 1 <= size_class s <= 30.
Proof. intros s Hs. apply (size_class_ok s Hs). Qed.
Lemma size_class_ge : forall s, 1 <= s <= kMaxSize -> s <= class_size (size_class s).
Proof. intros s Hs. apply (size_class_ok s Hs). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record crow := CRow { cr_lo : Z; cr_hi : Z; cr_class : Z; cr_rzlog : Z }.
Definition class_table : list crow :=
  [ CRow 0 16 1 0;        CRow 17 48 2 0;        CRow 49 64 3 1;        CRow 65 96 4 1;
    CRow 97 128 6 2;      CRow 129 160 7 2;      CRow 161 192 8 2;      CRow 193 224 9 2;
    CRow 225 256 10 2;    CRow 257 288 11 2;     CRow 289 320 12 2;     CRow 321 352 13 2;
    CRow 353 384 14 2;    CRow 385 416 15 2;     CRow 417 448 16 2;     CRow 449 640 17 3;
    CRow 641 896 18 3;    CRow 897 1408 19 3;    CRow 1409 1920 20 3;   CRow 1921 2944 21 3;
    CRow 2945 3968 22 3;  CRow 3969 5888 23 4;   CRow 5889 7936 24 4;   CRow 7937 12032 25 4;
    CRow 12033 16128 26 4; CRow 16129 24064 27 5; CRow 24065 32256 28 5; CRow 32257 48128 29 6;
    CRow 48129 64512 30 6 ].

Definition crow_ok (r : crow) : bool :=
  zall (cr_lo r) (cr_hi r) (fun n => (class_of n =? cr_class r) && (rz_log n =? cr_rzlog r)).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition row_of (n : Z) (r : crow) : bool := (cr_lo r <=? n) && (n <=? cr_hi r).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma class_of_range : forall n, 0 <= n <= kMaxPrimaryUser -> 1 <= class_of n <= 30.
Proof.
  intros n Hn. unfold class_of. apply size_class_range. pose proof (needed_size_ge n).
  pose proof (proj2 (from_primary_iff n) ltac:(lia)) as F. apply needed_size_primary_le in F. lia.
Qed.
Lemma class_of_fits : forall n, 0 <= n <= kMaxPrimaryUser -> needed_size n <= class_size (class_of n).
Proof.
  intros n Hn. unfold class_of. apply size_class_ge. pose proof (needed_size_ge n).
  pose proof (proj2 (from_primary_iff n) ltac:(lia)) as F. apply needed_size_primary_le in F. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chunk_addr (space_beg c k : Z) : Z := region_beg space_beg c + k * class_size c.
Definition compact_ptr (space_beg c alloc_beg : Z) : Z := (alloc_beg - region_beg space_beg c) / kCompactPtrScale.
Definition decompact (space_beg c cp : Z) : Z := space_beg + Z.shiftl c 32 + Z.shiftl cp 4.
(* [comment removed for export] *)
Definition class_of_addr (space_beg p : Z) : Z := Z.land (Z.shiftr (p - space_beg) 32) 31.
Definition chunk_idx (space_beg c p : Z) : Z := ((p - space_beg) mod 2^32) / class_size c.
Definition in_primary (space_beg p : Z) : Prop := space_beg <= p < space_beg + kSpaceSize.

Definition user_beg (alloc_beg n : Z) : Z := alloc_beg + rz_size n.
Definition chunk_beg (alloc_beg n : Z) : Z := user_beg alloc_beg n - kChunkHeaderSize.
(* [comment removed for export] *)
Definition sec_alloc_beg (map_beg : Z) : Z := map_beg + kPageSize.
Definition sec_user_beg (map_beg : Z) : Z := map_beg + kPageSize + 2048.

(* [comment removed for export] *)
Lemma chunk_addr_mod32 : forall sb c k, 1 <= c <= 30 -> 0 <= k -> sb mod 0x10000 = 0 -> chunk_addr sb c k mod 32 = 0.
Proof.
  intros sb c k Hc Hk Hsb. unfold chunk_addr, region_beg, kRegionSize.
  pose proof (class_size_mod32 c Hc) as M.
  rewrite Z.add_mod, (Z.add_mod sb) by lia.
  rewrite (mod0_down sb 0x10000 32 (divide_wit 32 2048) Hsb).
  replace (c * 2^32) with ((c * 2^27) * 32) by lia. rewrite Z_mod_mult.
  rewrite Zmult_mod, M, Z.mul_0_r. reflexivity.
Qed.
Lemma user_beg_mod16 : forall ab n, ab mod 32 = 0 -> user_beg ab n mod 16 = 0.
Proof.
  intros ab n H. unfold user_beg. rewrite Z.add_mod, rz_size_mod16 by lia.
  rewrite (mod0_down ab 32 16 (divide_wit 16 2) H). reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma user_end_fits : forall ab n, 0 <= n <= kMaxPrimaryUser ->
  user_beg ab n + user_size n <= ab + needed_size n /\ ab + needed_size n <= ab + class_size (class_of n).
Proof.
  intros ab n Hn. pose proof (class_of_fits n Hn). pose proof (rounded_user_size n ltac:(lia)).
  unfold user_beg, needed_size in *. lia.
Qed.
(* [comment removed for export] *)
Lemma sec_user_end_fits : forall mb n, kMaxPrimaryUser < n ->
  sec_user_beg mb + n <= sec_alloc_beg mb + needed_size2 n /\ sec_alloc_beg mb + needed_size2 n <= mb + map_size n.
Proof.
  intros mb n Hn. rewrite needed_size2_secondary by lia. pose proof (rounded_size_ge n).
  pose proof (map_size_room n) as R. rewrite needed_size2_secondary in R by lia.
  unfold sec_user_beg, sec_alloc_beg in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_to_shadow (a : Z) : Z := Z.shiftr a 3 + kShadowOffset.
Definition addr_is_in_low (a : Z) : Prop := 0 <= a <= kLowMemEnd.
Definition addr_is_in_high (a : Z) : Prop := kHighMemBeg <= a <= kHighMemEnd.
(* [comment removed for export] *)
Definition addr_is_in_mem (a : Z) : Prop := addr_is_in_low a \/ addr_is_in_high a.
(* [comment removed for export] *)
Definition shadow_len (size : Z) : Z := Z.shiftr size 3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition partial_granule (n : Z) : Z := Z.land n 7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition remap_path (size : Z) : bool := kClearShadowMmapThreshold <=? shadow_len size.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition q_put_bytes (n : Z) (new_batch : bool) : Z := n + (if new_batch then kQuarantineBatchBytes else 0).
(* [comment removed for export] *)
Definition q_transfer (thread_bytes : Z) : bool := kQuarantineCacheSize <? thread_bytes.
(* [comment removed for export] *)
Definition q_recycle (global_bytes : Z) : bool := kQuarantineMaxSize <? global_bytes.
(* [comment removed for export] *)
Definition q_merge (global_bytes nbatches : Z) : bool :=
  let overhead := nbatches * kQuarantineBatchBytes in
  (overhead <? global_bytes) && (global_bytes * kOverheadThresholdPercents <? overhead * (100 + kOverheadThresholdPercents)).
(* [comment removed for export] *)
