(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy.
Import ListNotations.
Open Scope bv_scope.

Definition memmove_entry := 0x244e4%Z.

Section ListFacts.
  Open Scope Z_scope.

  Definition slice (l : list byte) (o k : nat) : list byte := firstn k (skipn o l).

  Definition mm_result (us : list byte) (sof dof n : nat) : list byte := upd_bytes us dof (slice us sof n).

  #[using="Type"] Lemma slice_length : forall l o k, (o + k <= length l)%nat -> length (slice l o k) = k.
  Proof. intros. unfold slice. rewrite firstn_length, skipn_length. lia. Qed.

  #[using="Type"] Lemma nth_error_slice : forall l o k i, (i < k)%nat -> nth_error (slice l o k) i = nth_error l (o + i)%nat.
  Proof.
    intros l o k i Hi. unfold slice. rewrite nth_error_firstn.
    replace (Nat.ltb i k) with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
  Qed.

  #[using="Type"] Lemma slice_0 : forall l o, slice l o 0 = [].
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma nth_error_ext : forall (l1 l2 : list byte), length l1 = length l2 ->
    (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
  Proof.
    induction l1 as [|x l1 IH]; intros [|y l2] Hl H; cbn in Hl; try discriminate; [reflexivity|].
    pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal.
    apply IH; [lia|]. intros i Hi. apply (H (S i)). cbn. lia.
  Qed.

  #[using="Type"] Lemma slice_app : forall l o k1 k2, (o + k1 + k2 <= length l)%nat ->
    slice l o k1 ++ slice l (o + k1) k2 = slice l o (k1 + k2).
  Proof.
    intros l o k1 k2 H. apply nth_error_ext.
    - rewrite app_length, !slice_length by lia. reflexivity.
    - intros i Hi. rewrite app_length, !slice_length in Hi by lia.
      destruct (Nat.ltb_spec0 i k1).
      + rewrite nth_error_app1 by (rewrite slice_length; lia). rewrite !nth_error_slice by lia. reflexivity.
      + rewrite nth_error_app2 by (rewrite slice_length; lia). rewrite slice_length by lia.
        rewrite !nth_error_slice by lia. f_equal. lia.
  Qed.

  #[using="Type"] Lemma slice_1 : forall l o b, nth_error l o = Some b -> slice l o 1 = [b].
  Proof.
    intros l o b H. unfold slice. pose proof (nth_error_split _ _ _ H) as (pre & post & E & Hl).
    rewrite E at 1. rewrite skipn_app, skipn_all2, Hl, Nat.sub_diag by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma upd_bytes_nil : forall (bs : list byte) k, upd_bytes bs k [] = bs.
  Proof. intros. unfold upd_bytes. cbn. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

  #[using="Type"] Lemma upd_bytes_nth_out : forall (cs : list byte) k bs i, (k + length bs <= length cs)%nat -> (i < length cs)%nat ->
    (i < k \/ k + length bs <= i)%nat -> nth_error (upd_bytes cs k bs) i = nth_error cs i.
  Proof.
    intros cs k bs i H1 H2 H3. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length bs)); cbn [andb]; try reflexivity. exfalso; lia.
  Qed.

  #[using="Type"] Lemma upd_bytes_nth_in : forall (cs : list byte) k bs i, (k + length bs <= length cs)%nat ->
    (k <= i < k + length bs)%nat -> nth_error (upd_bytes cs k bs) i = nth_error bs (i - k)%nat.
  Proof.
    intros cs k bs i H1 H2. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length bs)); cbn [andb]; try reflexivity; exfalso; lia.
  Qed.

  #[using="Type"] Lemma upd_bytes_app : forall (cs : list byte) k xs ys, (k + length xs + length ys <= length cs)%nat ->
    upd_bytes (upd_bytes cs k xs) (k + length xs) ys = upd_bytes cs k (xs ++ ys).
  Proof.
    intros cs k xs ys H.
    assert (L1 : length (upd_bytes cs k xs) = length cs) by (apply upd_bytes_length; lia).
    apply nth_error_ext.
    - rewrite !upd_bytes_length; rewrite ?L1, ?app_length; lia.
    - intros i Hi. rewrite upd_bytes_length in Hi by (rewrite L1; lia). rewrite L1 in Hi.
      rewrite !upd_bytes_nth by (rewrite ?L1, ?app_length; lia).
      rewrite app_length.
      destruct (Nat.leb_spec0 (k + length xs) i); destruct (Nat.ltb_spec0 i (k + length xs + length ys));
      destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length xs)); destruct (Nat.ltb_spec0 i (k + (length xs + length ys)));
        cbn [andb]; try (exfalso; lia); try reflexivity.
      + rewrite nth_error_app2 by lia. f_equal. lia.
      + rewrite nth_error_app1 by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma upd_bytes_app_rev : forall (cs : list byte) k xs ys, (k + length xs + length ys <= length cs)%nat ->
    upd_bytes (upd_bytes cs (k + length xs) ys) k xs = upd_bytes cs k (xs ++ ys).
  Proof.
    intros cs k xs ys H.
    assert (L1 : length (upd_bytes cs (k + length xs) ys) = length cs) by (apply upd_bytes_length; lia).
    apply nth_error_ext.
    - rewrite !upd_bytes_length; rewrite ?L1, ?app_length; lia.
    - intros i Hi. rewrite upd_bytes_length in Hi by (rewrite L1; lia). rewrite L1 in Hi.
      rewrite !upd_bytes_nth by (rewrite ?L1, ?app_length; lia).
      rewrite app_length.
      destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length xs));
      destruct (Nat.leb_spec0 (k + length xs) i); destruct (Nat.ltb_spec0 i (k + length xs + length ys)); destruct (Nat.ltb_spec0 i (k + (length xs + length ys)));
        cbn [andb]; try (exfalso; lia); try reflexivity.
      + rewrite nth_error_app1 by lia. reflexivity.
      + rewrite nth_error_app2 by lia. f_equal. lia.
  Qed.

  #[using="Type"] Lemma upd_bytes_slice_same : forall (us : list byte) o k, (o + k <= length us)%nat ->
    upd_bytes us o (slice us o k) = us.
  Proof.
    intros us o k H. apply nth_error_ext.
    - rewrite upd_bytes_length by (rewrite slice_length; lia). reflexivity.
    - intros i Hi. rewrite upd_bytes_length in Hi by (rewrite slice_length; lia).
      rewrite upd_bytes_nth by (rewrite ?slice_length; lia). rewrite slice_length by lia.
      destruct (Nat.leb_spec0 o i); destruct (Nat.ltb_spec0 i (o + k)); cbn [andb]; try reflexivity.
      rewrite nth_error_slice by lia. f_equal. lia.
  Qed.

  #[using="Type"] Lemma slice_upd_bytes_out : forall (cs : list byte) k bs o j, (k + length bs <= length cs)%nat -> (o + j <= length cs)%nat ->
    (o + j <= k \/ k + length bs <= o)%nat -> slice (upd_bytes cs k bs) o j = slice cs o j.
  Proof.
    intros cs k bs o j H1 H2 H3. apply nth_error_ext.
    - rewrite !slice_length; rewrite ?upd_bytes_length; lia.
    - intros i Hi. rewrite slice_length in Hi by (rewrite upd_bytes_length; lia).
      rewrite !nth_error_slice by lia. apply upd_bytes_nth_out; lia.
  Qed.

  Definition usF (us : list byte) (sof dof k : nat) : list byte := upd_bytes us dof (slice us sof k).
  Definition usB (us : list byte) (sof dof n r : nat) : list byte := upd_bytes us (dof + r) (slice us (sof + r) (n - r)).

  #[using="Type"] Lemma usF_0 : forall us sof dof, usF us sof dof 0 = us.
  Proof. intros. unfold usF. rewrite slice_0. apply upd_bytes_nil. Qed.
  #[using="Type"] Lemma usB_n : forall us sof dof n, usB us sof dof n n = us.
  Proof. intros. unfold usB. rewrite Nat.sub_diag, slice_0. apply upd_bytes_nil. Qed.
  #[using="Type"] Lemma usB_0 : forall us sof dof n, usB us sof dof n 0 = mm_result us sof dof n.
  Proof. intros. unfold usB, mm_result. rewrite !Nat.add_0_r, Nat.sub_0_r. reflexivity. Qed.
  #[using="Type"] Lemma usF_n : forall us sof dof n, usF us sof dof n = mm_result us sof dof n.
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma usF_length : forall us sof dof k, (sof + k <= length us)%nat -> (dof + k <= length us)%nat ->
    length (usF us sof dof k) = length us.
  Proof. intros. unfold usF. apply upd_bytes_length. rewrite slice_length; lia. Qed.
  #[using="Type"] Lemma usB_length : forall us sof dof n r, (r <= n)%nat -> (sof + n <= length us)%nat -> (dof + n <= length us)%nat ->
    length (usB us sof dof n r) = length us.
  Proof. intros. unfold usB. apply upd_bytes_length. rewrite slice_length; lia. Qed.

  #[using="Type"] Lemma usF_step : forall us sof dof k j, (sof + k + j <= length us)%nat -> (dof + k + j <= length us)%nat ->
    (dof + k <= sof + k \/ sof + k + j <= dof)%nat ->
    upd_bytes (usF us sof dof k) (dof + k) (slice (usF us sof dof k) (sof + k) j) = usF us sof dof (k + j).
  Proof.
    intros us sof dof k j H1 H2 H3. unfold usF.
    rewrite slice_upd_bytes_out by (rewrite ?slice_length; lia).
    pose proof (slice_length us sof k ltac:(lia)) as L.
    rewrite <- L at 2. rewrite upd_bytes_app by (rewrite !slice_length; lia).
    rewrite slice_app by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma usB_step : forall us sof dof n r j, (j <= r)%nat -> (r <= n)%nat -> (sof + n <= length us)%nat -> (dof + n <= length us)%nat ->
    (sof + r <= dof + r)%nat ->
    upd_bytes (usB us sof dof n r) (dof + (r - j)) (slice (usB us sof dof n r) (sof + (r - j)) j) = usB us sof dof n (r - j).
  Proof.
    intros us sof dof n r j H0 H1 H2 H3 H4. unfold usB.
    rewrite slice_upd_bytes_out by (rewrite ?slice_length; lia).
    pose proof (slice_length us (sof + (r - j)) j ltac:(lia)) as L.
    replace (dof + r)%nat with (dof + (r - j) + length (slice us (sof + (r - j)) j))%nat by (rewrite L; lia).
    rewrite upd_bytes_app_rev by (rewrite !slice_length; lia).
    replace (sof + r)%nat with (sof + (r - j) + j)%nat by lia. rewrite slice_app by lia.
    replace (j + (n - r))%nat with (n - (r - j))%nat by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma usF_nth : forall us sof dof k i, (sof + k <= length us)%nat -> (dof + k <= length us)%nat -> (i < length us)%nat ->
    (i < dof \/ dof + k <= i)%nat -> nth_error (usF us sof dof k) i = nth_error us i.
  Proof. intros. unfold usF. apply upd_bytes_nth_out; rewrite ?slice_length; lia. Qed.
  #[using="Type"] Lemma usB_nth : forall us sof dof n r i, (r <= n)%nat -> (sof + n <= length us)%nat -> (dof + n <= length us)%nat -> (i < length us)%nat ->
    (i < dof + r \/ dof + n <= i)%nat -> nth_error (usB us sof dof n r) i = nth_error us i.
  Proof. intros. unfold usB. apply upd_bytes_nth_out; rewrite ?slice_length; lia. Qed.

  #[using="Type"] Lemma usF_step1 : forall us sof dof k b, (sof + k + 1 <= length us)%nat -> (dof + k + 1 <= length us)%nat ->
    (dof < sof)%nat -> nth_error us (sof + k)%nat = Some b ->
    upd_bytes (usF us sof dof k) (dof + k) [b] = usF us sof dof (k + 1).
  Proof.
    intros us sof dof k b H1 H2 H3 Hb. rewrite <- (usF_step us sof dof k 1) by lia. f_equal.
    symmetry. apply slice_1. rewrite usF_nth by lia. exact Hb.
  Qed.

  #[using="Type"] Lemma usB_step1 : forall us sof dof n r b, (1 <= r)%nat -> (r <= n)%nat -> (sof + n <= length us)%nat -> (dof + n <= length us)%nat ->
    (sof < dof)%nat -> nth_error us (sof + (r - 1))%nat = Some b ->
    upd_bytes (usB us sof dof n r) (dof + (r - 1)) [b] = usB us sof dof n (r - 1).
  Proof.
    intros us sof dof n r b H0 H1 H2 H3 H4 Hb. rewrite <- (usB_step us sof dof n r 1) by lia. f_equal.
    symmetry. apply slice_1. rewrite usB_nth by lia. exact Hb.
  Qed.

End ListFacts.

Section MemFacts.
  Open Scope Z_scope.

  #[using="Type"] Lemma bytes_at_sub : forall m U us (o k : nat), bytes_at rsegs m U us -> (o + k <= length us)%nat ->
    bytes_at rsegs m (U + Z.of_nat o) (slice us o k).
  Proof.
    intros m U us o k H Hk.
    rewrite <- (firstn_skipn o us) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite firstn_length_le in H by lia.
    rewrite <- (firstn_skipn k (skipn o us)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.

  #[using="Type"] Lemma u8arr_sub : forall m U us (o k : nat), u8arr rsegs m U us -> (o + k <= length us)%nat ->
    u8arr rsegs m (U + Z.of_nat o) (slice us o k).
  Proof.
    intros m U us o k [Hb Hw] Hk. split. { apply bytes_at_sub; assumption. }
    destruct Hw as (HU & HL & Hw). rewrite slice_length by lia. split; [lia|]. split; [lia|].
    intros i Hi. replace (U + Z.of_nat o + i) with (U + (Z.of_nat o + i)) by lia. apply Hw. lia.
  Qed.

  #[using="Type"] Lemma u8arr_read8 : forall m U us (o : nat) a, u8arr rsegs m U us -> (o + 8 <= length us)%nat ->
    a = wa (U + Z.of_nat o) -> ov_read_bytes rsegs m a 8 = Some (slice us o 8).
  Proof.
    intros m U us o a [Hb _] Ho ->. unfold slice. rewrite <- (Nat2Z.id o) at 2.
    apply (bytes_at_read rsegs m U us (Z.of_nat o) 8 Hb); lia.
  Qed.

  #[using="Type"] Lemma u8arr_read1 : forall m U us (o : nat) b a, u8arr rsegs m U us -> nth_error us o = Some b ->
    a = wa (U + Z.of_nat o) -> ov_read_bytes rsegs m a 1 = Some [b].
  Proof.
    intros m U us o b a H Hn ->. eapply (u8arr_read rsegs m U us (Z.of_nat o)); [exact H| rewrite Nat2Z.id; exact Hn| lia| reflexivity].
  Qed.

  #[using="Type"] Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : word, bs = le8 v.
  Proof.
    intros bs Hl. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
    rewrite <- store_bytes_8. change (width_bytes 64) with 8%nat.
    pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hl in Hr.
    change (256 ^ Z.of_nat 8) with (2^64) in Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small.
    2:{ rewrite bytes_le_to_Z_le_val. change (bv_modulus 64) with (2^64). lia. }
    rewrite <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
  Qed.

  #[using="Type"] Lemma le8_of_load8 : forall bs : list byte, length bs = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word bs)) = bs.
  Proof. intros bs Hl. destruct (le8_surj bs Hl) as [v ->]. rewrite load_u64. reflexivity. Qed.

  #[using="Type"] Lemma u8arr_after_munch : forall m m' U us (dof : nat) xs,
    u8arr rsegs m U us -> munch [(U + Z.of_nat dof, U + Z.of_nat dof + Z.of_nat (length xs))] m m' -> wmono rsegs m m' ->
    bytes_at rsegs m' (U + Z.of_nat dof) xs -> (dof + length xs <= length us)%nat ->
    u8arr rsegs m' U (upd_bytes us dof xs).
  Proof.
    intros m m' U us dof xs [Hb Hw] MU WM Hxs Hl.
    pose proof (bytes_at_bound _ _ _ _ Hb) as B.
    split.
    - destruct Hb as (HU & HL & Hb). split; [lia|]. split. { rewrite upd_bytes_length by lia. lia. }
      intros i Hi. rewrite upd_bytes_length in Hi by lia. rewrite upd_bytes_nth by lia.
      destruct (Nat.leb_spec0 dof i); destruct (Nat.ltb_spec0 i (dof + length xs)); cbn [andb].
      + destruct Hxs as (_ & _ & Hx). rewrite <- (Hx (i - dof)%nat) by lia. f_equal. unfold wa. f_equal. lia.
      + unfold mrd. rewrite MU. { apply Hb. lia. } cbn. rewrite wa_unsigned by lia. split; [lia| exact I].
      + unfold mrd. rewrite MU. { apply Hb. lia. } cbn. rewrite wa_unsigned by lia. split; [lia| exact I].
      + exfalso. lia.
    - destruct Hw as (HU & HL & Hw). rewrite upd_bytes_length by lia. split; [lia|]. split; [lia|].
      intros i Hi. apply WM. apply Hw. lia.
  Qed.
End MemFacts.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (U : Z) (us : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ u8arr rsegs m' U (mm_result us (Z.to_nat (bv_unsigned a1 - U)) (Z.to_nat (bv_unsigned a0 - U)) (Z.to_nat (bv_unsigned a2))).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (U : Z) (us : list byte).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation L := (Z.of_nat (length us)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis ARR : u8arr rsegs m U us.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis HU : (8 <= U)%Z.
  Hypothesis HS : (U <= S /\ S + n <= U + L)%Z.
  Hypothesis HD : (U <= D /\ D + n <= U + L)%Z.
  Hypothesis Hn : (n < 2^62)%Z.

  Definition sof := Z.to_nat (S - U).
  Definition dof := Z.to_nat (D - U).
  Definition nn := Z.to_nat n.

  Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 U us m).

  Notation ST pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition INV (m1 : word -> option byte) (us1 : list byte) : Prop :=
    u8arr rsegs m1 U us1 /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.

  #[using="m ARR HU HS HD"] Lemma bounds : (0 <= U /\ U + L <= 2^64 /\ 0 <= n /\ Z.of_nat sof = S - U /\ Z.of_nat dof = D - U /\ Z.of_nat nn = n
                  /\ (sof + nn <= length us)%nat /\ (dof + nn <= length us)%nat)%Z.
  Proof.
    pose proof (u8arr_bound _ _ _ _ ARR). pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R; cbn in R.
    unfold sof, dof, nn. lia.
  Qed.

  Ltac open_inv H := destruct H as (AR & MI & MU & WM).

  #[using="a1 ARR HU HS HD"] Lemma mm_store : forall m1 us1 (off : nat) xs a,
    INV m1 us1 -> length us1 = length us -> (off + length xs <= length us)%nat ->
    (D <= U + Z.of_nat off /\ U + Z.of_nat off + Z.of_nat (length xs) <= D + n)%Z ->
    a = wa (U + Z.of_nat off) ->
    store_ok rsegs m1 a (length xs) = true /\
    INV (write_to_mem m1 a xs) (upd_bytes us1 off xs).
  Proof.
    intros m1 us1 off xs a I Hl Ho Hin Ha; open_inv I. pose proof bounds as B.
    split.
    { eapply (u8arr_store_ok_n rsegs m1 U us1 (Z.of_nat off) (length xs) a AR); [lia| rewrite Hl; lia | rewrite Ha; f_equal; lia]. }
    subst a. split; [|split; [|split]].
    - rewrite <- (Nat2Z.id off) at 2. apply (u8arr_write_bytes rsegs m1 U us1 (Z.of_nat off) xs AR); [lia|]. rewrite Nat2Z.id, Hl. lia.
    - apply mem_inv_store; [exact MI|]. eapply (u8arr_store_ok_n rsegs m1 U us1 (Z.of_nat off)); [exact AR| lia| rewrite Hl; lia| reflexivity].
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  Ltac pg := match goal with |- ?G => idtac G end.

  Ltac mst_fin I2 xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace bs0 with xs by bytes_tac;
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : u8arr _ m1 _ _ |- _ => clear H
      | H : mem_inv _ m1 |- _ => clear H
      | H : munch _ _ m1 |- _ => clear H
      | H : wmono _ _ m1 |- _ => clear H
      | H : INV m1 _ |- _ => clear H
      | H : length _ = length us |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a xs) as m' eqn:E; clear E; try clear m1;
      pose proof I2 as I2'; destruct I2' as (AR & MI & MU & WM)
    end.
  Ltac by_byte := symmetry; apply le1_zxb.

  #[using="Type"] Lemma mm_ret : forall m1 x5 x11 x12 x13 x14 x15 x16 x17,
    INV m1 (mm_result us sof dof nn) ->
    evt rsegs POST (ST 0x24570 m1 x5 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x11 x12 x13 x14 x15 x16 x17 I; open_inv I.
    zstep. finish.
  Qed.

  #[using="ARR HU HS HD"] Lemma mm_fwd_bytes : forall (j k : nat) m1 x5 x11 x15 x16 x17,
    (nn - k = j)%nat -> (k < nn)%nat -> (dof < sof)%nat ->
    INV m1 (usF us sof dof k) ->
    evt rsegs POST (ST 0x2451c m1 x5 x11 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (S + Z.of_nat k)) x15 x16 x17).
  Proof.
    induction j as [|j IH]; intros k m1 x5 x11 x15 x16 x17 Hj Hk Hds I; [lia|]. pose proof bounds as B.
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usF us sof dof k) = length us) by (apply usF_length; lia).
    destruct (nth_error us (sof + k)) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8arr_read1 m1 U (usF us sof dof k) (sof + k) b (Z_to_bv 64 (S + Z.of_nat k)) AR
                  ltac:(rewrite usF_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep.
    destruct (mm_store m1 (usF us sof dof k) (dof + k) [b] (Z_to_bv 64 (D + Z.of_nat k)) I LEN1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    cbn [length] in SOK. zstep. mst_fin I2 [b] by_byte.
    rewrite (usF_step1 us sof dof k b) in I2; [| lia | lia | lia | exact Hb].
    zstep. zstep. if_cases K; zify_cond K.
    - replace (D + Z.of_nat k + 1)%Z with (D + Z.of_nat (k + 1))%Z by lia.
      replace (S + Z.of_nat k + 1)%Z with (S + Z.of_nat (k + 1))%Z by lia.
      apply (IH (k + 1)%nat); try lia. exact I2.
    -
      assert (k + 1 = nn)%nat by lia.
      zstep. apply mm_ret. rewrite <- usF_n. replace nn with (k + 1)%nat. exact I2.
  Qed.

  Ltac by_le8 := apply le8_of_load8; rewrite slice_length; [reflexivity| lia].

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_entry : forall (k : nat) m1 x5 x11 x15 x16 x17,
    (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    evt rsegs POST (ST 0x24514 m1 x5 x11 (Z_to_bv 64 (n - Z.of_nat k)) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (S + Z.of_nat k)) x15 x16 x17).
  Proof.
    intros k m1 x5 x11 x15 x16 x17 Hk Hds I. pose proof bounds as B.
    zstep. if_cases K; zify_cond K.
    - assert (k = nn) by lia. subst k. apply mm_ret. exact I.
    - zstep. replace (D + Z.of_nat k + (n - Z.of_nat k))%Z with (D + n)%Z by lia.
      apply (mm_fwd_bytes (nn - k) k); try lia. exact I.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_words : forall (j k : nat) m1 x5 x15 x16 x17,
    (nn - k = j)%nat -> (k + 8 <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    evt rsegs POST (ST 0x24644 m1 x5 (Z_to_bv 64 7) (Z_to_bv 64 (n - Z.of_nat k)) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (S + Z.of_nat k)) x15 x16 x17).
  Proof.
    induction j as [j IH] using lt_wf_ind; intros k m1 x5 x15 x16 x17 Hj Hk Hds I. pose proof bounds as B.
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usF us sof dof k) = length us) by (apply usF_length; lia).
    pose proof (u8arr_read8 m1 U (usF us sof dof k) (sof + k) (Z_to_bv 64 (S + Z.of_nat k)) AR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    set (ch := slice (usF us sof dof k) (sof + k) 8) in RD.
    assert (CL : length ch = 8%nat) by (subst ch; apply slice_length; lia).
    zstep. zstep.
    destruct (mm_store m1 (usF us sof dof k) (dof + k) ch (Z_to_bv 64 (D + Z.of_nat k)) I LEN1 ltac:(rewrite CL; lia) ltac:(rewrite CL; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    rewrite CL in SOK. zstep. mst_fin I2 ch ltac:(symmetry; apply le8_of_load8; exact CL).
    subst ch. rewrite (usF_step us sof dof k 8) in I2 by lia.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + Z.of_nat k + 8)%Z with (D + Z.of_nat (k + 8))%Z by lia.
      replace (S + Z.of_nat k + 8)%Z with (S + Z.of_nat (k + 8))%Z by lia.
      replace (n - Z.of_nat k + -8)%Z with (n - Z.of_nat (k + 8))%Z by lia.
      apply (IH (nn - (k + 8))%nat ltac:(lia) (k + 8)%nat); try lia. exact I2.
    - zstep. replace (D + Z.of_nat k + 8)%Z with (D + Z.of_nat (k + 8))%Z by lia.
      replace (S + Z.of_nat k + 8)%Z with (S + Z.of_nat (k + 8))%Z by lia.
      replace (n - Z.of_nat k + -8)%Z with (n - Z.of_nat (k + 8))%Z by lia.
      apply (mm_fwd_entry (k + 8)); try lia. exact I2.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_wentry : forall (k : nat) m1 x5 x11 x15 x16 x17,
    (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    evt rsegs POST (ST 0x24638 m1 x5 x11 (Z_to_bv 64 (n - Z.of_nat k)) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (S + Z.of_nat k)) x15 x16 x17).
  Proof.
    intros k m1 x5 x11 x15 x16 x17 Hk Hds I. pose proof bounds as B.
    zstep. zstep. if_cases K; zify_cond K.
    - apply mm_fwd_entry; try lia. exact I.
    - zstep. apply (mm_fwd_words (nn - k) k); try lia. exact I.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_head : forall (j k : nat) m1 x5 x13 x14 x17,
    (nn - k = j)%nat -> (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    evt rsegs POST (ST 0x24584 m1 x5 (Z_to_bv 64 (S + Z.of_nat k)) (Z_to_bv 64 (n - Z.of_nat k)) x13 x14
                       (Z_to_bv 64 (D + Z.of_nat k + 1)) (Z_to_bv 64 (D + Z.of_nat k)) x17).
  Proof.
    induction j as [|j IH]; intros k m1 x5 x13 x14 x17 Hj Hk Hds I; pose proof bounds as B.
    { zstep. if_cases K; zify_cond K; [| exfalso; lia]. apply mm_ret. replace nn with k by lia. exact I. }
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usF us sof dof k) = length us) by (apply usF_length; lia).
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    destruct (nth_error us (sof + k)) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8arr_read1 m1 U (usF us sof dof k) (sof + k) b (Z_to_bv 64 (S + Z.of_nat k)) AR
                  ltac:(rewrite usF_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep. zstep. zstep.
    destruct (mm_store m1 (usF us sof dof k) (dof + k) [b] (Z_to_bv 64 (D + Z.of_nat k)) I LEN1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    cbn [length] in SOK. zstep. mst_fin I2 [b] by_byte.
    rewrite (usF_step1 us sof dof k b) in I2; [| lia | lia | lia | exact Hb].
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - replace (D + Z.of_nat k + 2)%Z with (D + Z.of_nat (k + 1) + 1)%Z by lia.
      replace (D + Z.of_nat k + 1)%Z with (D + Z.of_nat (k + 1))%Z by lia.
      replace (S + Z.of_nat k + 1)%Z with (S + Z.of_nat (k + 1))%Z by lia.
      replace (n - Z.of_nat k + -1)%Z with (n - Z.of_nat (k + 1))%Z by lia.
      apply (IH (k + 1)%nat); try lia. exact I2.
    - zstep. replace (D + Z.of_nat k + 1)%Z with (D + Z.of_nat (k + 1))%Z by lia.
      replace (S + Z.of_nat k + 1)%Z with (S + Z.of_nat (k + 1))%Z by lia.
      replace (n - Z.of_nat k + -1)%Z with (n - Z.of_nat (k + 1))%Z by lia.
      apply (mm_fwd_wentry (k + 1)); try lia. exact I2.
  Qed.
  #[using="us"] Lemma neg_mod64_nz : forall x, (0 < x < 2^64)%Z -> ((0 - x) mod 18446744073709551616 <> 0)%Z.
  Proof.
    intros x Hx E. apply Z.mod_divide in E; [|lia]. destruct E as [k Hk]. nia.
  Qed.

  Ltac bwd_byte_body qq I :=
    let I' := fresh "I'" in let LEN1 := fresh "LEN1" in let b := fresh "b" in let Hb := fresh "Hb" in
    let RD := fresh "RD" in let SOK := fresh "SOK" in let I2 := fresh "I2" in
    pose proof I as I'; destruct I' as (AR & MI & MU & WM);
    assert (LEN1 : length (usB us sof dof nn (qq + 1)) = length us) by (apply usB_length; lia);
    destruct (nth_error us (sof + qq)) as [b|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; lia];
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (u8arr_read1 m1 U (usB us sof dof nn (qq + 1)) (sof + qq) b (Z_to_bv 64 (S + Z.of_nat qq)) AR
                  ltac:(rewrite usB_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD;
    zstep; zstep;
    destruct (mm_store m1 (usB us sof dof nn (qq + 1)) (dof + qq) [b] (Z_to_bv 64 (D + Z.of_nat qq)) I LEN1
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2];
    cbn [length] in SOK; zstep; mst_fin I2 [b] by_byte;
    replace (dof + qq)%nat with (dof + (qq + 1 - 1))%nat in I2 by lia;
    (rewrite (usB_step1 us sof dof nn (qq + 1) b) in I2;
      [| lia | lia | lia | lia | lia | replace (sof + (qq + 1 - 1))%nat with (sof + qq)%nat by lia; exact Hb]);
    replace (qq + 1 - 1)%nat with qq in I2 by lia;
    zstep; zstep; zstep
    end.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_bytes : forall (q : nat) m1 (x5 x14 x15 x16 x17 : word),
    (q + 1 <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn (q + 1)) ->
    evt rsegs POST (ST 0x24558 m1 x5 (Z_to_bv 64 (S + Z.of_nat q)) (Z_to_bv 64 (0 - Z.of_nat (q + 1))) (Z_to_bv 64 (D + Z.of_nat q)) x14 x15 x16 x17).
  Proof.
    induction q as [|q IH]; intros m1 x5 x14 x15 x16 x17 Hq Hsd I; pose proof bounds as B.
    - bwd_byte_body 0%nat I. if_cases K; zify_cond K.
      + exfalso. lia.
      + apply mm_ret. rewrite <- usB_0. exact I2.
    - bwd_byte_body (Datatypes.S q) I. if_cases K; zify_cond K.
      + replace (S + Z.of_nat (Datatypes.S q) + -1)%Z with (S + Z.of_nat q)%Z by lia.
        replace (D + Z.of_nat (Datatypes.S q) + -1)%Z with (D + Z.of_nat q)%Z by lia.
        replace (0 - Z.of_nat (Datatypes.S q + 1) + 1)%Z with (0 - Z.of_nat (q + 1))%Z by lia.
        apply IH; try lia. replace (q + 1)%nat with (Datatypes.S q) by lia. exact I2.
      + exfalso. replace (0 - Z.of_nat (Datatypes.S q + 1) + 1)%Z with (0 - Z.of_nat (Datatypes.S q))%Z in K by lia.
        revert K. apply neg_mod64_nz. lia.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_entry : forall (r : nat) m1 (x5 x11 x12 x14 x15 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) -> x11 = a1 ->
    evt rsegs POST (ST 0x24544 m1 x5 x11 x12 (Z_to_bv 64 (Z.of_nat r)) x14 x15 x16 x17).
  Proof.
    intros r m1 x5 x11 x12 x14 x15 x16 x17 Hr Hsd I ->. pose proof bounds as B.
    zstep. if_cases K; zify_cond K.
    - apply mm_ret. rewrite <- usB_0. replace 0%nat with r by lia. exact I.
    - zstep. zstep. zstep. zstep.
      destruct r as [|q]; [exfalso; lia|].
      replace (S + (Z.of_nat (Datatypes.S q) + -1))%Z with (S + Z.of_nat q)%Z by lia.
      replace (D + (Z.of_nat (Datatypes.S q) + -1))%Z with (D + Z.of_nat q)%Z by lia.
      replace (0 - Z.of_nat (Datatypes.S q))%Z with (0 - Z.of_nat (q + 1))%Z by lia.
      apply mm_bwd_bytes; try lia. replace (q + 1)%nat with (Datatypes.S q) by lia. exact I.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_words : forall (j r : nat) m1 (x5 x13 x17 : word),
    (r = j)%nat -> (8 <= r)%nat -> (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) ->
    evt rsegs POST (ST 0x24610 m1 x5 a1 (Z_to_bv 64 (Z.of_nat r)) x13 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) x17).
  Proof.
    induction j as [j IH] using lt_wf_ind; intros r m1 x5 x13 x17 Hj H8 Hr Hsd I; subst j. pose proof bounds as B.
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usB us sof dof nn r) = length us) by (apply usB_length; lia).
    pose proof (u8arr_read8 m1 U (usB us sof dof nn r) (sof + (r - 8)) (Z_to_bv 64 (S + -8 + Z.of_nat r)) AR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    set (ch := slice (usB us sof dof nn r) (sof + (r - 8)) 8) in RD.
    assert (CL : length ch = 8%nat) by (subst ch; apply slice_length; lia).
    zstep. zstep. zstep. zstep.
    destruct (mm_store m1 (usB us sof dof nn r) (dof + (r - 8)) ch (Z_to_bv 64 (D + -8 + Z.of_nat r)) I LEN1 ltac:(rewrite CL; lia) ltac:(rewrite CL; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    rewrite CL in SOK. zstep. mst_fin I2 ch ltac:(symmetry; apply le8_of_load8; exact CL).
    subst ch. rewrite (usB_step us sof dof nn r 8) in I2 by lia.
    zstep. zstep. if_cases K; zify_cond K.
    - replace (Z.of_nat r + -8)%Z with (Z.of_nat (r - 8))%Z by lia.
      apply (IH (r - 8)%nat ltac:(lia) (r - 8)%nat); try lia. exact I2.
    - zstep. replace (Z.of_nat r + -8)%Z with (Z.of_nat (r - 8))%Z by lia.
      apply (mm_bwd_entry (r - 8)); try lia; [exact I2| reflexivity].
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_wentry : forall (r : nat) m1 (x5 x13 x14 x15 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) ->
    evt rsegs POST (ST 0x245fc m1 x5 a1 (Z_to_bv 64 (Z.of_nat r)) x13 x14 x15 x16 x17).
  Proof.
    intros r m1 x5 x13 x14 x15 x16 x17 Hr Hsd I. pose proof bounds as B.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. apply mm_bwd_entry; try lia; [exact I| reflexivity].
    - zstep. zstep. zstep. apply (mm_bwd_words r r); try lia. exact I.
  Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_head : forall (r : nat) m1 (x5 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) ->
    evt rsegs POST (ST 0x245d4 m1 x5 a1 (Z_to_bv 64 (D + (Z.of_nat r - 1))) (Z_to_bv 64 (0 - Z.of_nat r)) (Z_to_bv 64 (S + (Z.of_nat r - 1)))
                       (Z_to_bv 64 (D + (Z.of_nat r - 1))) x16 x17).
  Proof.
    induction r as [|q IH]; intros m1 x5 x16 x17 Hr Hsd I; pose proof bounds as B.
    { zstep. if_cases K; zify_cond K; [| exfalso; lia]. apply mm_ret. rewrite <- usB_0. exact I. }
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usB us sof dof nn (Datatypes.S q)) = length us) by (apply usB_length; lia).
    zstep. if_cases K; zify_cond K. { exfalso. revert K. apply neg_mod64_nz. lia. }
    destruct (nth_error us (sof + q)) as [b|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; lia].
    pose proof (u8arr_read1 m1 U (usB us sof dof nn (Datatypes.S q)) (sof + q) b (Z_to_bv 64 (S + (Z.of_nat (Datatypes.S q) - 1))) AR
                  ltac:(rewrite usB_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep.
    destruct (mm_store m1 (usB us sof dof nn (Datatypes.S q)) (dof + q) [b] (Z_to_bv 64 (D + (Z.of_nat (Datatypes.S q) - 1))) I LEN1
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    cbn [length] in SOK. zstep. mst_fin I2 [b] by_byte.
    replace (dof + q)%nat with (dof + (Datatypes.S q - 1))%nat in I2 by lia.
    rewrite (usB_step1 us sof dof nn (Datatypes.S q) b) in I2;
      [| lia | lia | lia | lia | lia | replace (sof + (Datatypes.S q - 1))%nat with (sof + q)%nat by lia; exact Hb].
    replace (Datatypes.S q - 1)%nat with q in I2 by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - replace (D + (Z.of_nat (Datatypes.S q) - 1) + -1)%Z with (D + (Z.of_nat q - 1))%Z by lia.
      replace (S + (Z.of_nat (Datatypes.S q) - 1) + -1)%Z with (S + (Z.of_nat q - 1))%Z by lia.
      replace (0 - Z.of_nat (Datatypes.S q) + 1)%Z with (0 - Z.of_nat q)%Z by lia.
      apply IH; try lia. exact I2.
    - zstep.
      replace (Z_to_bv 64 (0 - (0 - Z.of_nat (Datatypes.S q) + 1) mod 18446744073709551616)) with (Z_to_bv 64 (Z.of_nat q)).
      2:{ apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_r. f_equal. lia. }
      apply mm_bwd_wentry; try lia. exact I2.
  Qed.

  Ltac reg_eq := first [ reflexivity | f_equal; lia | etransitivity; [symmetry; apply Z_to_bv_bv_unsigned|]; f_equal; lia ].

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_entry' : forall (k : nat) m1 (x5 x11 xa2 xa3 xa4 x15 x16 x17 : word),
    (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    xa2 = Z_to_bv 64 (n - Z.of_nat k) -> xa3 = Z_to_bv 64 (D + Z.of_nat k) -> xa4 = Z_to_bv 64 (S + Z.of_nat k) ->
    evt rsegs POST (ST 0x24514 m1 x5 x11 xa2 xa3 xa4 x15 x16 x17).
  Proof. intros; subst; apply mm_fwd_entry; assumption. Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_wentry' : forall (k : nat) m1 (x5 x11 xa2 xa3 xa4 x15 x16 x17 : word),
    (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    xa2 = Z_to_bv 64 (n - Z.of_nat k) -> xa3 = Z_to_bv 64 (D + Z.of_nat k) -> xa4 = Z_to_bv 64 (S + Z.of_nat k) ->
    evt rsegs POST (ST 0x24638 m1 x5 x11 xa2 xa3 xa4 x15 x16 x17).
  Proof. intros; subst; apply mm_fwd_wentry; assumption. Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_fwd_head' : forall (k : nat) m1 (x5 xa1 xa2 x13 x14 xa5 xa6 x17 : word),
    (k <= nn)%nat -> (dof < sof)%nat -> INV m1 (usF us sof dof k) ->
    xa1 = Z_to_bv 64 (S + Z.of_nat k) -> xa2 = Z_to_bv 64 (n - Z.of_nat k) ->
    xa5 = Z_to_bv 64 (D + Z.of_nat k + 1) -> xa6 = Z_to_bv 64 (D + Z.of_nat k) ->
    evt rsegs POST (ST 0x24584 m1 x5 xa1 xa2 x13 x14 xa5 xa6 x17).
  Proof. intros; subst; eapply (mm_fwd_head (nn - k) k); try assumption; reflexivity. Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_entry' : forall (r : nat) m1 (x5 x12 xa3 x14 x15 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) -> xa3 = Z_to_bv 64 (Z.of_nat r) ->
    evt rsegs POST (ST 0x24544 m1 x5 a1 x12 xa3 x14 x15 x16 x17).
  Proof. intros; subst; apply mm_bwd_entry; try assumption; reflexivity. Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_wentry' : forall (r : nat) m1 (x5 xa2 x13 x14 x15 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) -> xa2 = Z_to_bv 64 (Z.of_nat r) ->
    evt rsegs POST (ST 0x245fc m1 x5 a1 xa2 x13 x14 x15 x16 x17).
  Proof. intros; subst; apply mm_bwd_wentry; assumption. Qed.

  #[using="ARR HU HS HD Hn"] Lemma mm_bwd_head' : forall (r : nat) m1 (x5 xa2 xa3 xa4 xa5 x16 x17 : word),
    (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) ->
    xa2 = Z_to_bv 64 (D + (Z.of_nat r - 1)) -> xa3 = Z_to_bv 64 (0 - Z.of_nat r) ->
    xa4 = Z_to_bv 64 (S + (Z.of_nat r - 1)) -> xa5 = Z_to_bv 64 (D + (Z.of_nat r - 1)) ->
    evt rsegs POST (ST 0x245d4 m1 x5 a1 xa2 xa3 xa4 xa5 x16 x17).
  Proof. intros; subst; apply mm_bwd_head; assumption. Qed.

  #[using="us"] Lemma sep_of_test : forall s d k,
    (0 <= s < 2^64 -> 0 <= d < 2^64 -> 0 <= k < 2^62 -> s <> d ->
    (s - (k + d) mod 18446744073709551616) mod 18446744073709551616 <=
    (0 - (Z.shiftl k 1) mod 18446744073709551616) mod 18446744073709551616 ->
    s + k <= d \/ d + k <= s)%Z.
  Proof.
    intros s d k Hs Hd Hk NE H.
    rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1)%Z with 2%Z in H.
    rewrite !Zminus_mod_idemp_r in H.
    destruct (Z.eq_dec k 0) as [->|Hk0]; [lia|].
    Z.div_mod_to_equations. nia.
  Qed.

  #[using="ARR MI0"] Lemma INV_init : INV m us.
  Proof. split; [exact ARR|]. split; [exact MI0|]. split; [apply munch_refl| apply wmono_refl]. Qed.

  #[using="ARR MI0 HU HS HD Hn"] Lemma memmove_body :
    evt rsegs POST (ST 0x244e4 m t0 a1 a2 a3 a4 a5 a6 a7).
  Proof.
    pose proof bounds as B. pose proof INV_init as I.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
    unfold bv_modulus in R0, R1; cbn in R0, R1.
    zstep. if_cases Keq; zify_cond Keq.
    {   apply mm_ret. unfold mm_result. replace sof with dof by (unfold sof, dof; lia).
      rewrite upd_bytes_slice_same by lia. exact I. }
    zstep. zstep. zstep. zstep. zstep. if_cases Kcpy; zify_cond Kcpy.
    {
      apply sep_of_test in Kcpy; try lia.
      zstep.
      pose proof (bytes_at_sub m U us sof nn (proj1 ARR) ltac:(lia)) as SRC.
      replace (U + Z.of_nat sof)%Z with S in SRC by lia.
      pose proof (rw_cells_of_u8arr rsegs m _ _ (u8arr_sub m U us dof nn ARR ltac:(lia))) as DST.
      rewrite slice_length in DST by lia. replace (U + Z.of_nat dof)%Z with D in DST by lia.
      replace nn with (Z.to_nat n) in DST at 1 by reflexivity.
      eapply evt_mono.
      { apply (memcpy_spec ra sp gp tp _ t1 t2 s0 s1 a0 a1 a2 _ _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (slice us sof nn) (slice us dof nn) SRC ltac:(apply slice_length; lia) DST Kcpy MI0). }
      intros ms' PO. cbv beta in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MU & WM & MI & DST' & SRC').
      unfold memmove_post. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold mm_result. change (Z.to_nat (S - U)) with sof. change (Z.to_nat (D - U)) with dof. change (Z.to_nat n) with nn.
      apply (u8arr_after_munch m m' U us dof (slice us sof nn) ARR); [ | exact WM | | rewrite slice_length; lia].
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx |- *. rewrite slice_length in Hx by lia. lia.
      - apply u8arr_of_rw_cells in DST'. replace (U + Z.of_nat dof)%Z with D by lia. exact (proj1 DST'). }
    zstep. zstep. zstep. if_cases Kdir; zify_cond Kdir.
    -   zstep. if_cases Kal; zify_cond Kal.
      +   zstep. zstep. zstep. if_cases Kal2; zify_cond Kal2.
        * apply (mm_bwd_wentry' nn); try lia; [| reg_eq]. rewrite usB_n. exact I.
        * zstep. zstep. zstep. zstep. zstep. apply (mm_bwd_head' nn); try lia; try reg_eq. rewrite usB_n. exact I.
      + zstep. apply (mm_bwd_entry' nn); try lia; [| reg_eq]. rewrite usB_n. exact I.
    -   zstep. if_cases Kal; zify_cond Kal.
      + zstep. zstep. if_cases Kal2; zify_cond Kal2.
        * zstep. zstep. apply (mm_fwd_wentry' 0); try lia; try reg_eq. rewrite usF_0. exact I.
        * zstep. zstep. apply (mm_fwd_head' 0); try lia; try reg_eq. rewrite usF_0. exact I.
      + zstep. zstep. apply (mm_fwd_entry' 0); try lia; try reg_eq. rewrite usF_0. exact I.
  Qed.
End Proofs.

Lemma memmove_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (U : Z) (us : list byte),
  u8arr rsegs m U us ->
  (8 <= U)%Z ->
  (U <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= U + Z.of_nat (length us))%Z ->
  (U <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= U + Z.of_nat (length us))%Z ->
  (bv_unsigned a2 < 2^62)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 U us m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x244e4) fc None m (seg_rom rsegs)).
Proof. intros until us. intros ARR HU HS HD Hn MI. apply memmove_body; assumption. Qed.
