(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kMinSizeLog : Z := 5.
Definition kMidSizeLog : Z := 9.
Definition kMinSize : Z := 32.
Definition kMidSize : Z := 512.
Definition kMidClass : Z := 16.          (* [comment removed for export] *)
Definition kS : Z := 2.                  (* [comment removed for export] *)
Definition kMaxSize : Z := 65536.        (* [comment removed for export] *)
Definition kNumClasses : Z := 32.
Definition kLargestClassID : Z := 30.
Definition kRegionSizeLog : Z := 32.
Definition kRegionSize : Z := 2^32.
Definition kSpaceSize : Z := 2^37.
Definition kUserMapSize : Z := 2^18.     (* [comment removed for export] *)
Definition kFreeArrayMapSize : Z := 2^18.
Definition kFreeArraySize : Z := 2^29.   (* [comment removed for export] *)
Definition kFreeArrayOffset : Z := 0xE0000000.  (* [comment removed for export] *)
Definition kCompactPtrScale : Z := 4.    (* [comment removed for export] *)
Definition kMaxNumCachedHint : Z := 8.
Definition kMaxBytesCached : Z := 1024.  (* [comment removed for export] *)
Definition kChunkHeaderSize : Z := 16.
Definition kChunkHeader2Size : Z := 8.
Definition kMinRedzone : Z := 16.        (* [comment removed for export] *)
Definition kMaxRedzone : Z := 2048.      (* [comment removed for export] *)
Definition kPageSize : Z := 4096.
Definition kSecondaryAlign : Z := 8.
Definition kBatchClass : Z := 24.        (* [comment removed for export] *)
Definition kBatchSize : Z := 8192.
Definition kBatchCap : Z := 1021.        (* [comment removed for export] *)
Definition kPtrArrayCommit : Z := 2^17.  (* [comment removed for export] *)
Definition kChunksBlockCount : Z := 16384.
Definition kClearShadowMmapThreshold : Z := 2^64 - 1.  (* [comment removed for export] *)
Definition kMaxMallocFill : Z := 4096.   (* [comment removed for export] *)
Definition kMallocFillByte : Z := 0xbe.
Definition kQuarantineMax : Z := 2^28.   (* [comment removed for export] *)
Definition kQuarantineMin : Z := 0xE666661.  (* [comment removed for export] *)
Definition kThreadQuarantineMax : Z := 2^20. (* [comment removed for export] *)

Definition round_up (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition round_down (x a : Z) : Z := (x / a) * a.

(* [comment removed for export] *)
Fixpoint zseq (a : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => a :: zseq (a + 1) k' end.
Lemma In_zseq : forall k a x, a <= x < a + Z.of_nat k -> In x (zseq a k).
Proof.
  induction k as [|k IH]; intros a x H; cbn; [lia|].
  destruct (Z.eq_dec a x); [left; assumption| right]. apply IH. lia.
Qed.
Definition zrange (lo hi : Z) : list Z := zseq lo (Z.to_nat (hi + 1 - lo)).
Lemma In_zrange : forall lo hi x, lo <= x <= hi -> In x (zrange lo hi).
Proof. intros. unfold zrange. apply In_zseq. rewrite Z2Nat.id; lia. Qed.

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 64 - 16 then 0
  else if n <=? 128 - 32 then 1
  else if n <=? 512 - 64 then 2
  else if n <=? 4096 - 128 then 3
  else if n <=? 16384 - 256 then 4
  else if n <=? 32768 - 512 then 5
  else if n <=? 65536 - 1024 then 6
  else 7.
(* [comment removed for export] *)
Definition rz_size (n : Z) : Z := 16 * 2 ^ (rz_log n).

Definition req (n : Z) : Z := Z.max n 1.
Definition rounded (n : Z) : Z := round_up (Z.max n kChunkHeader2Size) 8.
Definition needed1 (n : Z) : Z := rounded n + rz_size n.
Definition from_primary (n : Z) : bool := needed1 n <=? kMaxSize.
Definition needed (n : Z) : Z := if from_primary n then needed1 n else needed1 n + rz_size n.

(* [comment removed for export] *)
Definition class_size (c : Z) : Z :=
  if c <=? kMidClass then kMinSize * c
  else let c' := c - kMidClass in
       let t := kMidSize * 2 ^ (c' / 2) in     (* [comment removed for export] *)
       t + (t / 2) * (c' mod 2).               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition msb (s : Z) : Z := Z.log2 s.

Definition class_id (s : Z) : Z :=
  if s <=? kMidSize then (s + kMinSize - 1) / kMinSize      (* [comment removed for export] *)
  else let l := msb s in
       let hbits := (s / 2 ^ (l - 1)) mod 2 in              (* [comment removed for export] *)
       let lbits := s mod 2 ^ (l - 1) in                    (* [comment removed for export] *)
       let l1 := l - kMidSizeLog in
       kMidClass + l1 * 2 + hbits + (if 0 <? lbits then 1 else 0).

Definition max_cached_hint (sz : Z) : Z :=
  if sz =? 0 then 0 else Z.max 1 (Z.min kMaxNumCachedHint (kMaxBytesCached / sz)).
Definition hint (c : Z) : Z := max_cached_hint (class_size c).
Definition max_count (c : Z) : Z := 2 * hint c.
Definition chunks_per_map (c : Z) : Z := kUserMapSize / class_size c.

(* [comment removed for export] *)
Definition malloc_class (n : Z) : Z := class_id (needed1 n).

(* [comment removed for export] *)
Definition map_size (n : Z) : Z := round_up (needed n) kPageSize + kPageSize.

(* [comment removed for export] *)
Definition region_beg (space_beg c : Z) : Z := space_beg + c * kRegionSize.
Definition free_array (space_beg c : Z) : Z := region_beg space_beg c + kFreeArrayOffset.
Definition chunk_of_compact (space_beg c x : Z) : Z := region_beg space_beg c + 16 * x.
Definition compact_of_chunk (space_beg c p : Z) : Z := (p - region_beg space_beg c) / 16.
(* [comment removed for export] *)
Definition in_primary (space_beg p : Z) : bool := (space_beg <=? p) && (p <? space_beg + kSpaceSize).
Definition class_of_addr (space_beg p : Z) : Z := ((p - space_beg) / kRegionSize) mod kNumClasses.

(* [comment removed for export] *)
Definition kShadowBase : Z := 0x7fff8000.
Definition kHighMemEnd : Z := 2^47 - 1.
Definition kHighMemBeg : Z := kShadowBase + kHighMemEnd / 8 + 1.   (* [comment removed for export] *)
Definition kLowMemEnd : Z := kShadowBase - 1.
Definition mem_to_shadow (a : Z) : Z := kShadowBase + a / 8.

(* [comment removed for export] *)
Definition kBigMapSize : Z := 0x80000.      (* [comment removed for export] *)
Definition shadow_page (a : Z) : Z := round_down (mem_to_shadow a) kPageSize.
Definition hull_pages (mb msz : Z) : list Z :=
  let p0 := shadow_page mb in
  let p1 := shadow_page (mb + msz - 1) in
  map (fun i => p0 + kPageSize * Z.of_nat i) (seq 0 (Z.to_nat ((p1 - p0) / kPageSize + 1))).
Definition residue_pages (mb msz : Z) : list Z :=
  if msz <? kBigMapSize then hull_pages mb msz else [shadow_page mb; shadow_page (mb + msz - 1)].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kCmPrim : Z := 10001.
Definition acharge (n : Z) : Z :=
  if from_primary n then kCmPrim
  else if map_size n <? kBigMapSize then 25 + map_size n / 4096 else 5 + map_size n / 4096 + map_size n / 32768.
Definition arefund (n : Z) : Z :=
  if from_primary n then 0
  else if map_size n <? kBigMapSize then map_size n / 4096 else map_size n / 4096 + map_size n / 32768.
(* [comment removed for export] *)
Definition aresidue_charge (n : Z) : Z := if from_primary n then 0 else if map_size n <? kBigMapSize then 20 else 2.
Definition addr_is_in_mem (a : Z) : bool := (a <=? kLowMemEnd) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).

(* [comment removed for export] *)
Definition kMurM : Z := 0xc6a4a7935bd1e995.
Definition kMurSeed : Z := 0x9747b28c9747b28c.
Definition w64 (z : Z) : Z := z mod 2^64.
Definition mur_mix (k : Z) : Z := let k1 := w64 (k * kMurM) in w64 (Z.lxor k1 (Z.shiftr k1 47) * kMurM).
Definition mur_add (h k : Z) : Z := w64 (Z.lxor h (mur_mix k) * kMurM).
Definition mur_get (h : Z) : Z := let x := w64 (Z.lxor h (Z.shiftr h 47) * kMurM) in Z.lxor x (Z.shiftr x 47).
Definition depot_hash (key : list Z) : Z :=
  let h0 := Z.lxor (w64 (8 * Z.of_nat (length key) * kMurM)) kMurSeed in
  mur_get (mur_add (fold_left mur_add key h0) 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kHighMemBeg_val : kHighMemBeg = 0x10007fff8000.
Proof. reflexivity. Qed.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_size_values : forall n, In (rz_size n) [16;32;64;128;256;512;1024;2048].
Proof.
  intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbn; tauto.
Qed.

Lemma rz_size_pos : forall n, 16 <= rz_size n <= 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbn; lia. Qed.

Lemma rz_size_mod16 : forall n, rz_size n mod 16 = 0.
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); reflexivity. Qed.

Lemma round_up_ge : forall x a, 0 < a -> x <= round_up x a.
Proof.
  intros x a Ha. unfold round_up.
  pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). nia.
Qed.
Lemma round_up_lt : forall x a, 0 < a -> round_up x a < x + a.
Proof.
  intros x a Ha. unfold round_up.
  pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). nia.
Qed.
Lemma round_up_mod : forall x a, 0 < a -> round_up x a mod a = 0.
Proof. intros. unfold round_up. apply Z_mod_mult. Qed.
Lemma round_up_id : forall x a, 0 < a -> x mod a = 0 -> round_up x a = x.
Proof.
  intros x a Ha Hm. unfold round_up.
  pose proof (Z.div_mod x a ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E.
  set (q := x / a) in *. rewrite E.
  replace (a * q + a - 1) with (q * a + (a - 1)) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma rounded_ge : forall n, Z.max n 8 <= rounded n /\ rounded n < Z.max n 8 + 8 /\ rounded n mod 8 = 0.
Proof.
  intros n. unfold rounded, kChunkHeader2Size. split; [apply round_up_ge; lia|]. split; [apply round_up_lt; lia| apply round_up_mod; lia].
Qed.

Lemma needed1_ge : forall n, n + 16 <= needed1 n.
Proof. intros n. unfold needed1. pose proof (rounded_ge n). pose proof (rz_size_pos n). lia. Qed.

Lemma needed1_mod8 : forall n, needed1 n mod 8 = 0.
Proof.
  intros n. unfold needed1. pose proof (rounded_ge n) as (_ & _ & H).
  rewrite Z.add_mod by lia. rewrite H.
  replace (rz_size n mod 8) with 0; [reflexivity|].
  unfold rz_size, rz_log. repeat (destruct (_ <=? _)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma from_primary_small : forallb (fun n => Bool.eqb (from_primary n) (n <=? 64512)) (zrange 0 65536) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma from_primary_iff : forall n, 0 <= n -> from_primary n = true <-> n <= 64512.
Proof.
  intros n Hn. destruct (Z.le_gt_cases n 65536).
  - pose proof from_primary_small as F. rewrite forallb_forall in F.
    specialize (F n (In_zrange 0 65536 n ltac:(lia))).
    apply Bool.eqb_prop in F. rewrite F. rewrite Z.leb_le. tauto.
  - unfold from_primary, kMaxSize. pose proof (needed1_ge n). rewrite Z.leb_le. lia.
Qed.

(* [comment removed for export] *)
Definition class_size_table : list Z :=
  [0; 32; 64; 96; 128; 160; 192; 224; 256; 288; 320; 352; 384; 416; 448; 480; 512;
   768; 1024; 1536; 2048; 3072; 4096; 6144; 8192; 12288; 16384; 24576; 32768; 49152; 65536; 98304].
Lemma class_size_table_ok : forall c, 0 <= c <= 31 -> class_size c = nth (Z.to_nat c) class_size_table 0.
Proof.
  intros c Hc.
  assert (E : exists k, (k < 32)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E as (k & Hk & ->). rewrite Nat2Z.id.
  do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma hint_table : forall c, 1 <= c <= 30 ->
  hint c = nth (Z.to_nat c) [0;8;8;8;8;6;5;4;4;3;3;2;2;2;2;2;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1] 0.
Proof.
  intros c Hc. assert (E : exists k, (k < 31)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E as (k & Hk & ->). rewrite Nat2Z.id. do 31 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma hint_range : forall c, 1 <= c <= 30 -> 1 <= hint c <= 8.
Proof. intros c Hc. rewrite hint_table by lia. assert (E : exists k, (k < 31)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E as (k & Hk & ->). rewrite Nat2Z.id. do 31 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && (if 1 <? c then class_size (c - 1) <? s else true).

Lemma class_ok_all : forallb class_ok (zrange 1 65536) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_id_spec : forall s, 1 <= s <= 65536 ->
  1 <= class_id s <= 30 /\ s <= class_size (class_id s) /\ (1 < class_id s -> class_size (class_id s - 1) < s).
Proof.
  intros s Hs. pose proof class_ok_all as H. rewrite forallb_forall in H.
  specialize (H s (In_zrange 1 65536 s Hs)). unfold class_ok in H. cbn zeta in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [lia|]. split; [exact H2|]. intros Hc. destruct (Z.ltb_spec 1 (class_id s)); [|lia]. apply Z.ltb_lt in H3. exact H3.
Qed.

Lemma class_size_mod : forall c, 1 <= c <= 30 -> class_size c mod 32 = 0 /\ 32 <= class_size c <= 65536.
Proof.
  intros c Hc. rewrite class_size_table_ok by lia.
  assert (E : exists k, (k < 31)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E as (k & Hk & ->). rewrite Nat2Z.id. do 31 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_class_ok : forall n, 0 <= n <= 64512 ->
  1 <= malloc_class n <= 30 /\ needed1 n <= class_size (malloc_class n).
Proof.
  intros n Hn. unfold malloc_class.
  assert (1 <= needed1 n <= 65536).
  { pose proof (needed1_ge n).
    assert (F : from_primary n = true) by (apply (proj2 (from_primary_iff n ltac:(lia))); lia).
    unfold from_primary, kMaxSize in F. apply Z.leb_le in F. lia. }
  pose proof (class_id_spec (needed1 n) H). tauto.
Qed.

(* [comment removed for export] *)
Example classes_of_our_sizes :
  map malloc_class [1; 8; 16; 17; 26; 32; 48; 104; 128; 256; 384; 512; 640; 768; 1024; 1536; 2048; 3072; 4096; 5889; 6016; 7936; 8064; 8192; 16384; 32768; 48256; 64512]
  = [1; 1; 1; 2; 2; 2; 2; 6; 6; 10; 14; 17; 17; 18; 19; 20; 21; 22; 23; 24; 24; 24; 25; 25; 27; 29; 30; 30].
Proof. vm_compute. reflexivity. Qed.

Example map_sizes_of_our_sizes :
  map map_size [64513; 65536; 131072; 262144; 524288; 1048576; 2097152; 0x3fd80; 0x41e80]
  = [0x12000; 0x12000; 0x22000; 0x42000; 0x82000; 0x102000; 0x202000; 0x42000; 0x44000].
Proof. vm_compute. reflexivity. Qed.

Example secondary_from_64513 : from_primary 64512 = true /\ from_primary 64513 = false.
Proof. split; reflexivity. Qed.

Example chunks_per_map_table :
  map chunks_per_map [1; 2; 3; 6; 10; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30]
  = [8192; 4096; 2730; 1365; 819; 585; 341; 256; 170; 128; 85; 64; 42; 32; 21; 16; 10; 8; 5; 4].
Proof. vm_compute. reflexivity. Qed.
