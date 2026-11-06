(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.AS Require PropExec.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Bytes.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition seg_rw_byte (SEGS : list Segment) (z : Z) : bool :=
  match find_segment SEGS z 1 with
  | Some s => (seg_writable s && seg_readable s &&
               match segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s))) with Some _ => true | None => false end)%bool
  | None => false
  end.
(* [comment removed for export] *)
Fixpoint seg_rw_go (SEGS : list Segment) (a : Z) (fuel : nat) : bool :=
  match fuel with O => true | S f => (seg_rw_byte SEGS a && seg_rw_go SEGS (a + 1) f)%bool end.
Definition seg_rw_ok (SEGS : list Segment) (a n : Z) : bool :=
  (Z.leb 0 a && Z.leb 0 n && Z.leb (a + n) (2 ^ 64) && seg_rw_go SEGS a (Z.to_nat n))%bool.

Lemma seg_rw_go_sound : forall SEGS f a, seg_rw_go SEGS a f = true -> forall i, 0 <= i < Z.of_nat f -> seg_rw_byte SEGS (a + i) = true.
Proof.
  induction f as [|f IH]; intros a H i Hi; [lia|]. cbn [seg_rw_go] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; exact H1|].
  replace (a + i) with ((a + 1) + (i - 1)) by lia. apply (IH _ H2). lia.
Qed.

Lemma seg_rw_byte_sound : forall SEGS m z, 0 <= z < 2 ^ 64 -> seg_rw_byte SEGS z = true ->
  wview SEGS m (wa z) <> None /\ exists b, mrd SEGS m (wa z) = Some b.
Proof.
  intros SEGS m z Hz H. unfold seg_rw_byte in H.
  destruct (find_segment SEGS z 1) as [s|] eqn:F; [|discriminate].
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [Hw Hr].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) as [bb|] eqn:Hby; [|discriminate].
  assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; exact Hz).
  unfold wview, mrd. destruct (m (wa z)) as [b0|].
  - split; [discriminate| exists b0; reflexivity].
  - match goal with |- context [find_segment SEGS ?x 1] => assert (Ex : x = z) by exact Hu; rewrite Ex end.
    rewrite F, Hw, Hby. split; [discriminate|].
    exists bb. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
    match goal with |- context [find_segment SEGS ?x 1] => assert (Ex2 : x = z) by exact Hu; rewrite Ex2 end.
    rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hby. reflexivity.
Qed.

Lemma seg_rw_ok_sound : forall SEGS a n, seg_rw_ok SEGS a n = true -> forall m, wr_at SEGS m a n /\ stk SEGS m a (a + n).
Proof.
  intros SEGS a n H m. unfold seg_rw_ok in H.
  apply andb_prop in H as [H Hall]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  assert (G : forall i, 0 <= i < n -> wview SEGS m (wa (a + i)) <> None /\ exists b, mrd SEGS m (wa (a + i)) = Some b).
  { intros i Hi. apply seg_rw_byte_sound; [lia|]. apply (seg_rw_go_sound _ _ _ Hall). lia. }
  split.
  - split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (G i Hi)).
  - split; [lia|]. split; [lia|]. intros x Hx. replace x with (a + (x - a)) by lia. apply G. lia.
Qed.

(* [comment removed for export] *)
Lemma stk_bytes_n : forall SEGS m a n, stk SEGS m a (a + Z.of_nat n) -> exists bs, length bs = n /\ bytes_at SEGS m a bs.
Proof.
  intros SEGS m a n (H1 & H2 & H).
  exists (map (fun i => match mrd SEGS m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; lia). rewrite seq_nth by lia. cbn [option_map Nat.add].
  destruct (H (a + Z.of_nat i) ltac:(lia)) as [_ [b Hb]]. rewrite Hb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_blob : forall SEGS (m : word -> option byte) a (n : nat), seg_rw_ok SEGS a (Z.of_nat n) = true -> exists bs, rw_cells SEGS m a [CB n bs].
Proof.
  intros SEGS m a n H. destruct (seg_rw_ok_sound SEGS a (Z.of_nat n) H m) as [W S].
  destruct (stk_bytes_n SEGS m a n S) as (bs & Hl & B). exists bs.
  split; [split; [cbn [cells_wf cell_wf]; split; [exact Hl | exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_c1 : forall SEGS (m : word -> option byte) a, seg_rw_ok SEGS a 1 = true -> exists v, rw_cells SEGS m a [C1 v].
Proof.
  intros SEGS m a H. destruct (seg_rw_ok_sound SEGS a 1 H m) as [W S].
  destruct (stk_bytes_n SEGS m a 1 S) as (bs & Hl & B). destruct bs as [|b [|]]; try (cbn in Hl; lia).
  exists b. split; [split; [cbn; tauto|]; cbn [cells_bytes cbytes]; exact B | exact W].
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (AS.PropExec.bytes_le_to_Z_nonneg bs) as Hn.
  assert (E : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8) = bv_unsigned b + 256 * bytes_le_to_Z bs)
    by (apply Bytes.lor_shiftl8_add; lia).
  rewrite E. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    apply Z.div_unique with (r := bv_unsigned b); lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_c4 : forall SEGS (m : word -> option byte) a, seg_rw_ok SEGS a 4 = true -> exists v, rw_cells SEGS m a [C4 v].
Proof.
  intros SEGS m a H. destruct (seg_rw_ok_sound SEGS a 4 H m) as [W S].
  destruct (stk_bytes_n SEGS m a 4 S) as (bs & Hl & B).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split; [cbn; tauto|] | exact W].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4.
  pose proof (AS.PropExec.bytes_le_to_Z_bound bs) as Bd. pose proof (AS.PropExec.bytes_le_to_Z_nonneg bs) as Bn. rewrite Hl in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Bd; lia).
  rewrite <- Hl at 1. rewrite Z_to_le_bytes_of_bytes. exact B.
Qed.
