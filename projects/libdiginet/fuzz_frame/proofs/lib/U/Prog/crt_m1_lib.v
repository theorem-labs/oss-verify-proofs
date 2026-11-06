(* facts for the segment crt_m1 of check_round_trip in fuzz_frame.ubsan (the struct spec_frame at w, the header h that the stores leave at sp, the byte ranges of the frame at buf, the values of the flag registers). *)
(* Facts for crt_m1 (check_round_trip in fuzz_frame.ubsan, 0x13240 .. 0x1333c): the struct
   spec_frame at w with cmd and ncmds read as one halfword, the bytes of the header h that the
   stores leave at sp + 4, the byte ranges of the frame at buf, and the values that snez, seqz
   and slti leave. The UBSan twin of Prog/crt_m1_lib.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c crt_defs.
Import ListNotations.
Open Scope Z_scope.

Ltac crt_uns := rewrite ?unsigned_lit by lia.
Ltac crt_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; crt_uns; solve_cond_rec]
  end.
Ltac crt_dj := cbn [disjoint_from cells_size csize]; repeat split; lia.

Lemma crt_sys_short : forall b, (length (fr_body b) < 4)%nat -> crt_sys b = 0.
Proof.
  intros b H. unfold crt_sys, system_at. replace (length (fr_body b) - 3)%nat with 0%nat by lia. reflexivity.
Qed.

(* spec_cells with cmd and ncmds (w + 40, w + 41) as one C2 cell, the halfword that
   `lh a5, 0x28(s2)` reads, and body_len as the length of the body. *)
Definition crt_cells (buf : Z) (b : list byte) : list cell :=
  [ C4 (Z_to_bv 64 0); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 6));
    C2 (Z_to_bv 64 (fr_ethertype b)); C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b));
    C2 (Z_to_bv 64 (fr_retry b)); C4 (Z_to_bv 64 (fr_send b)); C4 (Z_to_bv 64 (fr_ack b));
    C2 (Z_to_bv 64 (fr_cmd b + 256 * fr_ncmds b));
    CB 6 (repeat (b8 0) 6); C8 (Z_to_bv 64 (buf + 30)); C8 (Z_to_bv 64 (Z.of_nat (length (fr_body b))));
    C8 (Z_to_bv 64 (fr_pad_len b)); C2 (Z_to_bv 64 (fr_body_sum b)); CB 6 (repeat (b8 0) 6) ].

Lemma le2_pair : forall c d, 0 <= c < 2^8 -> 0 <= d < 2^8 -> le2 (Z_to_bv 64 (c + 256 * d)) = [b8 c; b8 d].
Proof.
  intros c d Hc Hd. unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. unfold b8.
  f_equal; [|f_equal].
  - apply Z_to_bv8_mod. replace (c + 256 * d) with (c + d * 2^8) by lia. apply Z_mod_plus_full.
  - f_equal. rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.div_unique with (r := c); lia.
Qed.

Lemma crt_cells_of : forall m w buf b, fr_code b = 0 ->
  ro_cells rsegs m w (spec_cells buf b) -> ro_cells rsegs m w (crt_cells buf b).
Proof.
  intros m w buf b Hc [Hwf Hb]. split.
  - cbn. repeat split.
  - replace (cells_bytes (crt_cells buf b)) with (cells_bytes (spec_cells buf b)); [exact Hb|].
    unfold spec_cells, crt_cells. cbn [cells_bytes cbytes].
    rewrite le2_pair by first [exact (at8_range b 28) | exact (at8_range b 29)].
    rewrite (length_fr_body b Hc), Z2Nat.id by (destruct (fr_body_len_ok b Hc); lia).
    reflexivity.
Qed.

Lemma le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4, sx32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 _) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by lia.
  f_equal. unfold bv_swrap. change (bv_half_modulus 32) with (2^31). change (bv_wrap 32 ?x) with (x mod 2^32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma le2_sx16 : forall v : word, le2 (sx16 v) = le2 v.
Proof.
  intros v. unfold le2, sx16. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite (Z_to_le_bytes_mod 2 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 _) 16) by lia.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned v) 16) by lia.
  f_equal. unfold bv_swrap. change (bv_half_modulus 16) with (2^15). change (bv_wrap 16 ?x) with (x mod 2^16).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* The 12 bytes that the stores at sp + 4 .. sp + 0xf leave: send, ack, retry, then cmd and
   ncmds, each as loaded (sign-extended) from spec_cells. *)
Lemma crt_hb_cells : forall b,
  le4 (sx32 (Z_to_bv 64 (fr_send b))) ++ le4 (sx32 (Z_to_bv 64 (fr_ack b))) ++
  le2 (sx16 (Z_to_bv 64 (fr_retry b))) ++ le2 (sx16 (Z_to_bv 64 (fr_cmd b + 256 * fr_ncmds b))) = crt_hb b.
Proof.
  intros b. unfold crt_hb. rewrite !le4_sx32, !le2_sx16.
  assert (R1 : 0 <= fr_send b < 2^32) by exact (be32_range b 18).
  assert (R2 : 0 <= fr_ack b < 2^32) by exact (be32_range b 22).
  assert (R3 : 0 <= fr_retry b < 2^16) by exact (be16_range b 26).
  assert (R4 : 0 <= fr_cmd b < 2^8) by exact (at8_range b 28).
  assert (R5 : 0 <= fr_ncmds b < 2^8) by exact (at8_range b 29).
  rewrite le2_pair by lia.
  rewrite <- (le4_lit (fr_send b)), <- (le4_lit (fr_ack b)), <- (le2_lit (fr_retry b)) by lia.
  reflexivity.
Qed.

(* The frame cell at sp after the six stores at sp .. sp + 0xf, as crt_m1_post states it. *)
Lemma crt_frame_fold : forall m A (x0 x1 x3 x4 x2 x5 : word) sv hb,
  hb = le4 x3 ++ le4 x4 ++ le2 x2 ++ le2 x5 ->
  rw_cells rsegs m A (C2 x0 :: C2 x1 :: C4 x3 :: C4 x4 :: C2 x2 :: C2 x5 :: sv) ->
  rw_cells rsegs m A (CB 4 (le2 x0 ++ le2 x1) :: CB 12 hb :: sv).
Proof.
  intros m A x0 x1 x3 x4 x2 x5 sv hb -> [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (_ & _ & _ & _ & _ & _ & Hsv).
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite !length_app, !length_le2, !length_le4.
    split; [reflexivity|]. split; [reflexivity|]. exact Hsv.
  - cbn [cells_bytes cbytes] in *. rewrite <- !app_assoc. exact Hb.
  - match goal with |- wr_at _ _ _ (Z.of_nat ?s) => replace s with
      (cells_size (C2 x0 :: C2 x1 :: C4 x3 :: C4 x4 :: C2 x2 :: C2 x5 :: sv))
      by (cbn [cells_size csize]; lia) end.
    exact Hw.
Qed.

Lemma crt_hb_at : forall m A j' hb sv, rw_cells rsegs m A (CB 4 j' :: CB 12 hb :: sv) ->
  bytes_at rsegs m (A + 4) hb.
Proof.
  intros m A j' hb sv [[Hwf Hb] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hj & _ & _).
  cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite Hj in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma bytes_at_sub : forall m a l k len, bytes_at rsegs m a l -> (k + len <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn len (skipn k l)).
Proof.
  intros m a l k len H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn len (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* The dst, src and body bytes of the frame b at buf. *)
Lemma crt_frame_parts : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m buf (fr_dst b) /\ bytes_at rsegs m (buf + 6) (fr_src b) /\
  bytes_at rsegs m (buf + 30) (fr_body b) /\ length (fr_dst b) = 6%nat /\ length (fr_src b) = 6%nat.
Proof.
  intros m buf b Hc H.
  destruct (fr_code_ok b Hc) as (L30 & _ & _ & _).
  destruct (fr_body_len_ok b Hc) as (B0 & P0 & BL).
  pose proof (bytes_at_sub m buf b 0 6 H ltac:(lia)) as D. cbn [skipn] in D.
  change (Z.of_nat 0) with 0 in D. rewrite Z.add_0_r in D.
  pose proof (bytes_at_sub m buf b 6 6 H ltac:(lia)) as Sr.
  pose proof (bytes_at_sub m buf b 30 (Z.to_nat (fr_body_len b)) H ltac:(lia)) as Bd.
  unfold fr_dst, fr_src, fr_body.
  split; [exact D|].
  split; [exact Sr|]. split; [exact Bd|].
  rewrite length_firstn, length_firstn, length_skipn. lia.
Qed.

(* slti of a value under 2^63: the signed and the unsigned value are the same. *)
Lemma slti_small : forall v imm, 0 <= v < 2^63 -> v_slti (Z_to_bv 64 v) imm = if v <? imm then Z_to_bv 64 1 else Z_to_bv 64 0.
Proof.
  intros v imm H. unfold v_slti, zsig. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec v (2^63)); [reflexivity | lia].
Qed.

(* snez of a value that is not 0 (0x132a4). *)
Lemma crt_snez : forall v, 0 < v < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 v) = Z_to_bv 64 1.
Proof.
  intros v H. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec 0 v); [reflexivity | lia].
Qed.

(* seqz of a value that is not 0 (0x132b4). *)
Lemma crt_seqz : forall v, 0 < v < 2^64 -> v_sltiu (Z_to_bv 64 v) 1 = Z_to_bv 64 0.
Proof.
  intros v H. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec v 1); [lia | reflexivity].
Qed.

(* not of a word (0x1329c). *)
Lemma crt_not : forall v, 0 <= v < 2^64 ->
  Z.lxor (bv_unsigned (Z_to_bv 64 v)) 18446744073709551615 = 2^64 - 1 - v.
Proof. intros v H. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. lia. Qed.

(* `mv a4, sp` leaves sp itself in a4; diginet_frame_build's contract reads it as hp. *)
Lemma crt_a4_sp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F pc fc rv m ro,
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (bv_unsigned sp)) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv m ro) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 sp a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv m ro).
Proof. intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F pc fc rv m ro H. rewrite Z_to_bv_lit_self in H. exact H. Qed.
