(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_map_str_to_int H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.

Fixpoint wv_check (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match wview rsegs (fun _ => None) (wa a) with Some _ => wv_check (a + 1) n' | None => false end
  end.

Lemma wv_check_sound : forall n a (m : mem) i,
  wv_check a n = true -> (0 <= i < Z.of_nat n)%Z -> wview rsegs m (wa (a + i)) <> None.
Proof.
  induction n as [|n IH]; intros a m i H Hi; [cbn in Hi; lia|].
  cbn [wv_check] in H. destruct (wview rsegs (fun _ => None) (wa a)) as [b0|] eqn:E; [| discriminate].
  destruct (Z.eq_dec i 0) as [->|NE].
  - rewrite Z.add_0_r. unfold wview in *. destruct (m (wa a)); [discriminate|]. rewrite E. discriminate.
  - replace (a + i)%Z with (a + 1 + (i - 1))%Z by lia. apply IH; [exact H| lia].
Qed.

Lemma wr_at_of_check : forall m a n, wv_check a (Z.to_nat n) = true -> (0 <= a)%Z -> (a + n <= 2^64)%Z -> (0 <= n)%Z -> wr_at rsegs m a n.
Proof.
  intros m a n H Ha Hn N0. split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (wv_check_sound (Z.to_nat n)); [exact H| lia].
Qed.

Lemma wv_check_data : wv_check 0x2a000 (Z.to_nat 0x33000) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wr_at_data : forall m a n, (0x2a000 <= a)%Z -> (a + n <= 0x5d000)%Z -> (0 <= n)%Z -> wr_at rsegs m a n.
Proof.
  intros m a n H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i)%Z with (0x2a000 + (a - 0x2a000 + i))%Z by lia. apply (wv_check_sound (Z.to_nat 0x33000)); [exact wv_check_data| lia].
Qed.

Lemma rw_cells_of_bytes : forall m a cs,
  cells_wf cs -> bytes_at rsegs m a (cells_bytes cs) -> (0x2a000 <= a)%Z -> (a + Z.of_nat (cells_size cs) <= 0x5d000)%Z -> rw_cells rsegs m a cs.
Proof.
  intros m a cs WF B H1 H2. split; [split; [exact WF| exact B]|]. apply wr_at_data; lia.
Qed.

Lemma u64arr_of_bytes : forall m a ws,
  bytes_at rsegs m a (u64s ws) -> (0x2a000 <= a)%Z -> (a + 8 * Z.of_nat (length ws) <= 0x5d000)%Z -> u64arr rsegs m a ws.
Proof. intros m a ws B H1 H2. split; [exact B|]. apply wr_at_data; lia. Qed.

Definition HDR_WS : list word := map (Z_to_bv 64)
  [0x10311; 25; 0x104b7; 27; 0x10511; 26; 0x1049e; 28; 0x10630; 29; 0x10415; 1; 0x10318; 2; 0x103b6; 30; 0x10466; 31; 0x105fb; 3;
   0x1060a; 32; 0x10477; 33; 0x1059f; 4; 0x1063e; 5; 0x10357; 6; 0x1045d; 7; 0x103a3; 34; 0x10442; 11; 0x104c6; 12; 0x10439; 13;
   0x1061b; 14; 0x1061e; 15; 0x10380; 35; 0x10521; 17; 0x105ac; 16; 0x1032d; 18; 0x106cc; 19; 0x106bb; 20; 0x10643; 36; 0x10539; 21;
   0x104ca; 22; 0x103c7; 24; 0x10485; 23]%Z.
Definition MT_WS : list word := map (Z_to_bv 64)
  [0x106d7; 1; 0x106be; 2; 0x104dc; 3; 0x103ac; 5; 0x10489; 9; 0x104ae; 8; 0x10582; 4; 0x106c2; 6; 0x10492; 7; 0x10582; 11; 0x103da; 0]%Z.

Definition GIFV : word := Z_to_bv 64 0xffffffff.
Definition GMAX_VAL : Z := 64000.

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma hdr_ws_bytes : u64s HDR_WS = gd_bytes 0x2b1a8 528.
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
Lemma mt_ws_bytes : u64s MT_WS = gd_bytes 0x2b3b8 176.
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
Lemma gif_bytes : le4 GIFV ++ map (Z_to_bv 8) [0; 0; 0; 0]%Z ++ le8 (Z_to_bv 64 GMAX_VAL) = gd_bytes 0x2b468 16.
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
Lemma zero_bytes : repeat (Z_to_bv 8 0) 12 = gd_bytes 0x3b700 12.
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
Lemma got_bytes : le8 (Z_to_bv 64 0x2b468) ++ le8 (Z_to_bv 64 0x2b470) = gd_bytes 0x2a118 16.
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.

Lemma rodata_bytes_at : forall m A bs,
  mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at rsegs m A bs.
Proof.
  intros m A bs MI RB HA HL. pose proof (ro_cells_image rsegs m A bs MI RB HA HL) as [_ B].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Fixpoint img_cstr (S : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom rsegs (wa S) with
           | Some b => if (bv_unsigned b =? 0)%Z then [] else b :: img_cstr (S + 1) f
           | None => []
           end
  end.
Definition img_pad (S : Z) (len : nat) : list byte :=
  match image_bytes rsegs (S + Z.of_nat len + 1) (Z.to_nat ((- (S + Z.of_nat len + 1)) mod 8)) with Some bs => bs | None => [] end.

Lemma notin_zero : forall (l : list byte), existsb (fun b => (bv_unsigned b =? 0)%Z) l = false -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H IN. apply Bool.not_true_iff_false in H. apply H. apply existsb_exists. exists (Z_to_bv 8 0). split; [exact IN| reflexivity].
Qed.

Fixpoint allz (p : Z -> Prop) (n : nat) (j : Z) : Prop :=
  match n with O => True | S n' => p j /\ allz p n' (j + 1) end.
Lemma allz_sound : forall p n j, allz p n j -> forall i, (j <= i < j + Z.of_nat n)%Z -> p i.
Proof.
  induction n as [|n IH]; intros j H i Hi; [cbn in Hi; lia|]. destruct H as [H0 H1].
  destruct (Z.eq_dec i j) as [->|NE]; [exact H0|]. apply (IH (j + 1)%Z H1). lia.
Qed.

Definition entry_ok (ws : list word) (i : Z) : Prop :=
  exists S str slack,
    nth_error ws (Z.to_nat (2 * i)) = Some (Z_to_bv 64 S)
    /\ (forall m, mem_inv rsegs m -> bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack)) /\ ~ In (Z_to_bv 8 0) str
    /\ ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z
    /\ (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x106e0)%Z.

Ltac zlen_lia := repeat match goal with |- context [Z.of_nat ?l] => let v := eval vm_compute in (Z.of_nat l) in change (Z.of_nat l) with v end; lia.
Ltac solve_entry S :=
  exists S, (img_cstr S 40), (img_pad S (length (img_cstr S 40)));
  split; [vm_compute; reflexivity|];
  split; [intros m MI; apply (rodata_bytes_at m); [exact MI| vm_compute; reflexivity| lia| zlen_lia]|];
  split; [apply notin_zero; vm_compute; reflexivity|];
  split; zlen_lia.

Lemma hdr_entries : forall i, (0 <= i < 33)%Z -> entry_ok HDR_WS i.
Proof.
  apply (allz_sound (entry_ok HDR_WS) 33 0). cbn [allz Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- entry_ok _ ?i =>
         let S := eval vm_compute in (match nth_error HDR_WS (Z.to_nat (2 * i)) with Some w => bv_unsigned w | None => 0%Z end) in
         solve_entry S end.
Qed.

Lemma mt_entries : forall i, (0 <= i < 11)%Z -> entry_ok MT_WS i.
Proof.
  apply (allz_sound (entry_ok MT_WS) 11 0). cbn [allz Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- entry_ok _ ?i =>
         let S := eval vm_compute in (match nth_error MT_WS (Z.to_nat (2 * i)) with Some w => bv_unsigned w | None => 0%Z end) in
         solve_entry S end.
Qed.

Lemma hdr_table_strings : forall B, (0x106e0 <= B)%Z -> table_strings HDR_WS 33 B.
Proof.
  intros B HB i Hi. destruct (hdr_entries i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5).
  exists S, str, slack. repeat (split; [assumption|]). lia.
Qed.
Lemma mt_table_strings : forall B, (0x106e0 <= B)%Z -> table_strings MT_WS 11 B.
Proof.
  intros B HB i Hi. destruct (mt_entries i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5).
  exists S, str, slack. repeat (split; [assumption|]). lia.
Qed.

Lemma hdr_ids : forall i, (0 <= i < 33)%Z -> exists id, nth_error HDR_WS (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id < 64)%Z.
Proof.
  apply (allz_sound _ 33 0). cbn [allz Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- exists id, nth_error _ ?k = _ /\ _ =>
         let v := eval vm_compute in (match nth_error HDR_WS k with Some w => bv_unsigned w | None => 0%Z end) in
         exists v; split; [vm_compute; reflexivity| lia] end.
Qed.
Lemma mt_ids : forall i, (0 <= i < 11)%Z -> exists id, nth_error MT_WS (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id <= 11)%Z.
Proof.
  apply (allz_sound _ 11 0). cbn [allz Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- exists id, nth_error _ ?k = _ /\ _ =>
         let v := eval vm_compute in (match nth_error MT_WS k with Some w => bv_unsigned w | None => 0%Z end) in
         exists v; split; [vm_compute; reflexivity| lia] end.
Qed.

Lemma HDR_WS_length : length HDR_WS = 66%nat. Proof. reflexivity. Qed.
Lemma MT_WS_length : length MT_WS = 22%nat. Proof. reflexivity. Qed.

Lemma hdr_tab_facts : forall B, (0x106e0 <= B)%Z ->
  length HDR_WS = 66%nat
  /\ (forall i, (0 <= i < 33)%Z -> exists id, nth_error HDR_WS (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id < 64)%Z)
  /\ table_strings HDR_WS 33 B.
Proof. intros B HB. split; [reflexivity|]. split; [exact hdr_ids| apply hdr_table_strings; exact HB]. Qed.
Lemma meth_tab_facts : forall B, (0x106e0 <= B)%Z ->
  length MT_WS = 22%nat
  /\ (forall i, (0 <= i < 11)%Z -> exists id, nth_error MT_WS (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id <= 11)%Z)
  /\ table_strings MT_WS 11 B.
Proof. intros B HB. split; [reflexivity|]. split; [exact mt_ids| apply mt_table_strings; exact HB]. Qed.

Lemma GD_statics : forall m, GD m ->
  u64arr rsegs m 0x2b1a8 HDR_WS
  /\ (exists zb, bytes_at rsegs m 0x3b700 [zb])
  /\ u64arr rsegs m 0x2b3b8 MT_WS
  /\ bytes_at rsegs m 0x2a118 (le8 (Z_to_bv 64 0x2b468)) /\ bytes_at rsegs m 0x2b468 (le4 GIFV)
  /\ rw_cells rsegs m 0x2b470 [C8 (Z_to_bv 64 GMAX_VAL)] /\ rw_cells rsegs m 0x3b708 [C1 (Z_to_bv 8 0)]
  /\ bytes_at rsegs m 0x2a120 (le8 (Z_to_bv 64 0x2b470)).
Proof.
  intros m G. unfold GD, GD_ranges in G.
  pose proof (proj1 (Forall_forall _ _) G) as F. cbn [fst snd] in F.
  pose proof (F (0x2b1a8, 528%nat) ltac:(cbn; LiaTuning.ctauto)) as G1. pose proof (F (0x2b3b8, 176%nat) ltac:(cbn; LiaTuning.ctauto)) as G2.
  pose proof (F (0x2b468, 16%nat) ltac:(cbn; LiaTuning.ctauto)) as G3. pose proof (F (0x3b700, 12%nat) ltac:(cbn; LiaTuning.ctauto)) as G4.
  pose proof (F (0x2a118, 16%nat) ltac:(cbn; LiaTuning.ctauto)) as G5. cbn [fst snd] in G1, G2, G3, G4, G5. clear F G.
  rewrite <- hdr_ws_bytes in G1. rewrite <- mt_ws_bytes in G2. rewrite <- gif_bytes in G3. rewrite <- zero_bytes in G4. rewrite <- got_bytes in G5.
  apply bytes_at_app in G3. destruct G3 as [G3a G3b]. apply bytes_at_app in G3b. destruct G3b as [_ G3c].
  rewrite length_le4 in G3c. cbn [length map Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G3c.
  apply bytes_at_app in G5. destruct G5 as [G5a G5b]. rewrite length_le8 in G5b. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G5b.
  change (repeat (Z_to_bv 8 0) 12) with ([Z_to_bv 8 0] ++ (repeat (Z_to_bv 8 0) 7 ++ ([Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 3))) in G4.
  apply bytes_at_app in G4. destruct G4 as [G4a G4b]. apply bytes_at_app in G4b. destruct G4b as [_ G4c].
  apply bytes_at_app in G4c. destruct G4c as [G4d _]. cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Nat.add] in G4d.
  split; [apply u64arr_of_bytes; [exact G1| lia| rewrite HDR_WS_length; cbn; lia]|].
  split; [eexists; exact G4a|].
  split; [apply u64arr_of_bytes; [exact G2| lia| rewrite MT_WS_length; cbn; lia]|].
  split; [exact G5a|]. split; [exact G3a|].
  split. { apply rw_cells_of_bytes; [cbn; repeat split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact G3c| lia| cbn; lia]. }
  split. { apply rw_cells_of_bytes; [cbn; repeat split; exact I| cbn [cells_bytes cbytes app le1]; exact G4d| lia| cbn; lia]. }
  exact G5b.
Qed.

Definition gd_addr (a : Z) : Prop :=
  (0x2b1a8 <= a < 0x2b1a8 + 528 \/ 0x2b3b8 <= a < 0x2b3b8 + 176 \/ 0x2b468 <= a < 0x2b468 + 16 \/ 0x3b700 <= a < 0x3b700 + 12 \/ 0x2a118 <= a < 0x2a118 + 16)%Z.

Lemma GD_ext : forall m m', GD m -> (forall a, gd_addr a -> m' (wa a) = m (wa a)) -> GD m'.
Proof.
  intros m m' G EXT. unfold GD in *. apply Forall_forall. intros [a n] IN. pose proof (proj1 (Forall_forall _ _) G (a, n) IN) as B. cbn [fst snd] in *.
  destruct B as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (B2 i Hi). unfold mrd. rewrite EXT; [reflexivity|].
  pose proof (image_bytes_length rsegs n a) as LEN. unfold gd_bytes in Hi.
  destruct (image_bytes rsegs a n) as [bs|] eqn:E; [| cbn in Hi; lia]. specialize (LEN bs eq_refl). rewrite LEN in Hi.
  unfold GD_ranges in IN. unfold gd_addr. cbn in IN.
  destruct IN as [IN|[IN|[IN|[IN|[IN|[]]]]]]; injection IN as <- <-; lia.
Qed.
