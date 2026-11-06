(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module AsanTab.

Definition SB : Z := 0x7fff8000.
Definition shad (a : Z) : Z := a / 8 + SB.

Definition BIG_LO : Z := 0x7fff7000.
Definition BIG_HI : Z := 0x10007fff8000.
Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighMemBeg : Z := 0x10007fff8000.
Definition kHighMemEnd : Z := 2 ^ 47 - 1.

Definition in_mem (a : Z) : bool := (a <=? kLowMemEnd) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).

Definition app_mem (a n : Z) : Prop := a + n <= BIG_LO \/ BIG_HI <= a.

Lemma kHighMemBeg_eq : kHighMemBeg = shad kHighMemEnd + 1.
Proof. reflexivity. Qed.
Lemma in_mem_app : forall a n i, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 -> app_mem a n -> 0 <= i < n -> in_mem (a + i) = true.
Proof.
  intros a n i Ha Hn Htop [H|H] Hi; unfold in_mem, kLowMemEnd, kHighMemBeg, kHighMemEnd, BIG_LO, BIG_HI in *;
  apply orb_true_iff; [left|right]; [apply Z.leb_le; lia | apply andb_true_iff; split; apply Z.leb_le; lia].
Qed.

Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2 ^ rz_log n.
Definition round_up (x m : Z) : Z := (x + m - 1) / m * m.

Definition needed0 (n : Z) (al16 : bool) : Z := round_up (Z.max n 8) 8 + rz_size n + (if al16 then 16 else 0).
Definition kMaxSize : Z := 0x10000.
Definition from_primary (n : Z) (al16 : bool) : bool := needed0 n al16 <=? kMaxSize.

Definition needed (n : Z) (al16 : bool) : Z := if from_primary n al16 then needed0 n al16 else needed0 n al16 + rz_size n.

Definition user_off (n : Z) : Z := rz_size n.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
Lemma rz_size_values : forall n, In (rz_size n) [16; 32; 64; 128; 256; 512; 1024; 2048].
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbn; tauto. Qed.

Definition kNumClasses : Z := 32.
Definition class_size (c : Z) : Z :=
  if c <=? 16 then 32 * c
  else let t := Z.shiftl 512 ((c - 16) / 2) in t + (if Z.odd (c - 16) then t / 2 else 0).

Definition class_id (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := Z.log2 s in
       let hbit := (Z.shiftr s (l - 1)) mod 2 in
       let lbits := s mod 2 ^ (l - 1) in
       2 * l - 2 + hbit + (if lbits =? 0 then 0 else 1).

Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / class_size c)).

Definition kRegionSize : Z := 2 ^ 32.
Definition kFreeArrayOffset : Z := 0xE0000000.
Definition kFreeArraySize : Z := 2 ^ 29.
Definition kUserMapSize : Z := 2 ^ 18.
Definition kSpaceSize : Z := 2 ^ 37.
Definition kSpaceReserve : Z := 0x2000011000.
Definition region_beg (space_beg c : Z) : Z := space_beg + c * kRegionSize.
Definition chunk_addr (space_beg c i : Z) : Z := region_beg space_beg c + i * class_size c.
Definition compact (space_beg c p : Z) : Z := (p - region_beg space_beg c) / 16.
Definition rinfo (space_beg c : Z) : Z := space_beg + kSpaceSize + 128 * c.

Definition chunks_per_map (c : Z) : Z := kUserMapSize / class_size c.

Definition sec_map_size (needed_sz : Z) : Z := round_up needed_sz 4096 + 4096.
Definition sec_user (map_beg n : Z) : Z := map_beg + 4096 + rz_size n.

Definition kQuarantineMax : Z := 2 ^ 28.
Definition kQuarantineMin : Z := 0xE666661.
Definition kLocalQuarantineMax : Z := 2 ^ 20.
Definition kBatchSlots : Z := 1021.
Definition kBatchBytes : Z := 8192.

Definition fs_log : Z := 20.
Definition fs_frame_bytes (k : Z) : Z := 64 * 2 ^ k.
Definition fs_nframes (k : Z) : Z := 2 ^ (fs_log - 6 - k).
Definition fs_flags_off (k : Z) : Z := 4096 + (2 ^ (fs_log - 5) - 2 ^ (fs_log - 5 - k)).
Definition fs_frame (fs k i : Z) : Z := fs + 4096 + 2 ^ (fs_log - 5) + k * 2 ^ fs_log + i * fs_frame_bytes k.
Definition fs_size : Z := 0xb09000.

Definition kDepotL2Nodes : Z := 2 ^ 16.
Definition kStoreBlockFrames : Z := 2 ^ 20.
Definition kMaxTraceDepth : Z := 30.

Fixpoint ziota (lo : Z) (k : nat) : list Z := match k with O => [] | S k' => lo :: ziota (lo + 1) k' end.
Definition zrange (lo n : Z) : list Z := ziota lo (Z.to_nat n).
Lemma in_ziota : forall k lo x, lo <= x < lo + Z.of_nat k -> In x (ziota lo k).
Proof. induction k as [|k IH]; intros lo x H; [lia|]. cbn. destruct (Z.eq_dec lo x); [left; assumption | right; apply IH; lia]. Qed.

Lemma class_size_table :
  map class_size (zrange 1 30)
  = [32; 64; 96; 128; 160; 192; 224; 256; 288; 320; 352; 384; 416; 448; 480; 512;
     768; 1024; 1536; 2048; 3072; 4096; 6144; 8192; 12288; 16384; 24576; 32768; 49152; 65536].
Proof. vmc_refl. Qed.

Lemma max_cached_table :
  map max_cached (zrange 1 30) = [16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2].
Proof. vmc_refl. Qed.

Lemma chunks_per_map_table :
  map chunks_per_map [1; 2; 3; 6; 7; 8; 16; 19; 21; 23; 24; 30] = [8192; 4096; 2730; 1365; 1170; 1024; 512; 170; 85; 42; 32; 4].
Proof. vmc_refl. Qed.

Definition class_ok (s : Z) : bool :=
  let c := class_id s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && ((c =? 1) || (class_size (c - 1) <? s)).
Lemma class_id_ok_all : forallb class_ok (zrange 1 65536) = true.
Proof. vmc_refl. Qed.

Lemma class_id_ok : forall s, 1 <= s <= 65536 ->
  1 <= class_id s <= 30 /\ s <= class_size (class_id s) /\ (class_id s = 1 \/ class_size (class_id s - 1) < s).
Proof.
  intros s Hs.
  assert (Hin : In s (zrange 1 65536)).
  { unfold zrange. apply in_ziota. lia. }
  pose proof class_id_ok_all as H. rewrite forallb_forall in H. specialize (H s Hin). unfold class_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  apply orb_prop in H4. destruct H4 as [H4|H4]; [apply Z.eqb_eq in H4 | apply Z.ltb_lt in H4]; lia.
Qed.

Lemma examples :
  from_primary 65536 false = false /\ sec_map_size (needed 65536 false) = 73728
  /\ class_id (needed 3 false) = 1 /\ class_id (needed 64 false) = 3 /\ class_id (needed 144 true) = 7
  /\ class_id (needed 100 false) = 6 /\ class_id (needed 1000 false) = 19 /\ class_id (needed 4999 false) = 23
  /\ class_id 8192 = 24 /\ needed 65536 false = 69632.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma round_up_8_spec : forall x, 0 <= x -> x <= round_up x 8 < x + 8 /\ round_up x 8 mod 8 = 0.
Proof. intros x Hx. unfold round_up. pose proof (Z.div_mod (x + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 8 - 1) 8 ltac:(lia)). split; [nia|]. apply Z.mod_mul. lia. Qed.

End AsanTab.
