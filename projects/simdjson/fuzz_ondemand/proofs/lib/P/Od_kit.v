(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_stage1_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Record odenv : Type := mkOdEnv {
  o_ra : word; o_sp : word; o_gp : word; o_tp : word;
  o_s0 : word; o_s1 : word; o_s2 : word; o_s3 : word; o_s4 : word; o_s5 : word;
  o_s6 : word; o_s7 : word; o_s8 : word; o_s9 : word; o_s10 : word; o_s11 : word;
  o_lo : Z;
  o_BUF : Z; o_SB : Z; o_CAP : Z; o_IMPL : Z; o_IDX : Z; o_icap : nat;
  o_COPY : Z;
  o_act : Z;
  o_bs : list Z; o_idxs : list Z;
  o_vptr : word; o_p12 : list byte; o_nxt : word; o_mid : list byte; o_docj : list byte;
  o_j304 : list byte; o_w320 : word; o_w328 : word; o_w336 : word; o_w344 : word;
  o_hi : list cell;
  o_m0 : mem
}.

Notation o_len E := (blen (o_bs E)).
Notation o_n E := (tokn (o_idxs E)).

Record od_ok_g (FS NEED GTOP VPTR : Z) (E : odenv) : Prop := mkOdOk {
  ook_bytes : bytes_ok (o_bs E);
  ook_s1 : S1OUT (o_bs E) (o_idxs E);
  ook_len : (o_len E <= S1_LEN_MAX)%Z;
  ook_glo : (GTOP <= o_lo E)%Z;
  ook_room : (o_lo E + NEED + FS <= bv_unsigned (o_sp E))%Z;
  ook_sp : (bv_unsigned (o_sp E) < 2^63)%Z;
  ook_buf : (0 <= o_BUF E /\ o_BUF E + o_len E + 64 <= o_lo E)%Z;
  ook_sb : (0 <= o_SB E /\ o_SB E + o_CAP E <= o_lo E)%Z;
  ook_cap : (o_len E + 62 <= o_CAP E)%Z;
  ook_sb_img : (o_SB E + o_CAP E <= 0x10000 \/ GTOP <= o_SB E)%Z;
  ook_impl : (0 <= o_IMPL E /\ o_IMPL E + 96 <= o_lo E)%Z;
  ook_idx : (0 <= o_IDX E /\ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_lo E)%Z;
  ook_icap : (o_n E + 3 <= Z.of_nat (o_icap E))%Z;
  ook_act : (0 <= o_act E <= 12)%Z;
  ook_vptr : o_vptr E = Z_to_bv 64 VPTR;
  ook_sb_buf : (o_SB E + o_CAP E <= o_BUF E \/ o_BUF E + o_len E + 64 <= o_SB E)%Z;
  ook_sb_idx : (o_SB E + o_CAP E <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_SB E)%Z;
  ook_sb_impl : (o_SB E + o_CAP E <= o_IMPL E \/ o_IMPL E + 96 <= o_SB E)%Z
}.

Definition dpi_cells (E : odenv) : list cell :=
  [C8 (o_vptr E); C4 (wz (o_n E)); CB 4 (o_p12 E); C8 (wz (o_IDX E)); C4 (o_nxt E); CB 44 (o_mid E);
   C8 (wz (o_BUF E)); C8 (wz (o_len E)); CB 8 (o_docj E)].

Definition idx_ok (E : odenv) (ws : list word) : Prop :=
  length ws = o_icap E /\ firstn (length (o_idxs E) + 3) ws = map wz (o_idxs E ++ [o_len E; o_len E; 0%Z]).

Lemma idx_ok_nth : forall E ws k, idx_ok E ws -> (0 <= k <= o_n E + 2)%Z ->
  nth_error ws (Z.to_nat k) = Some (wz (tokI (o_bs E) (o_idxs E) k)).
Proof.
  intros E ws k [HL HF] Hk. unfold tokn in Hk.
  assert (KL : (Z.to_nat k < length (o_idxs E) + 3)%nat) by lia.
  rewrite <- (firstn_skipn (length (o_idxs E) + 3) ws).
  rewrite nth_error_app1 by (rewrite HF, length_map, length_app; cbn [length]; lia).
  rewrite HF. rewrite nth_error_map. unfold tokI.
  rewrite (nth_error_nth' _ 0%Z) by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Lemma tokI_read_g : forall segs (m : mem) E ws k,
  u32arr segs m (o_IDX E) ws -> idx_ok E ws -> (0 <= k <= o_n E + 2)%Z ->
  ov_read_bytes segs m (wa (o_IDX E + 4 * k)) 4 = Some (le4 (wz (tokI (o_bs E) (o_idxs E) k))).
Proof.
  intros segs m E ws k HA HI Hk.
  eapply (u32arr_read segs m (o_IDX E) ws k); [exact HA| apply idx_ok_nth; assumption| lia| reflexivity].
Qed.

Lemma tokB_read_g : forall segs (m : mem) E off,
  bytes_at segs m (o_BUF E) (padded_bytes (o_bs E)) -> (0 <= off < o_len E + 64)%Z ->
  ov_read_bytes segs m (wa (o_BUF E + off)) 1 = Some [Z_to_bv 8 (B (o_bs E) off)].
Proof. intros segs m E off H Hoff. apply buf_read_g; assumption. Qed.

Section Ranges.
  Variable E : odenv.
  Hypothesis HS : S1OUT (o_bs E) (o_idxs E).
  Hypothesis HB : bytes_ok (o_bs E).
  Hypothesis HL : (o_len E <= S1_LEN_MAX)%Z.

  Lemma od_n_range : (1 <= o_n E <= o_len E)%Z.
  Proof using HS. split; [apply (tokn_pos _ _ HS)| apply (tokn_le_len _ _ HS)]. Qed.

  Lemma od_tokI_range : forall k, (0 <= k <= o_n E + 2)%Z -> (0 <= tokI (o_bs E) (o_idxs E) k <= o_len E)%Z.
  Proof using HS. intros k Hk. apply (tokI_bound _ _ HS). exact Hk. Qed.

  Lemma od_tokT_range : forall k, (0 <= tokT (o_bs E) (o_idxs E) k < 256)%Z.
  Proof using HB. intros k. unfold tokT. apply B_range. exact HB. Qed.

  Lemma od_B_range : forall i, (0 <= B (o_bs E) i < 256)%Z.
  Proof using HB. intros i. apply B_range. exact HB. Qed.
End Ranges.

Definition od_dead (n : Z) (st : ost) : Prop :=
  o_alive st = false /\ o_depth st = 0%Z /\ o_err st = TAPE_ERROR /\ (0 <= o_sbo st)%Z.

Definition od_arm_out (bs idxs : list Z) (st st' : ost) : Prop :=
  (o_pos st <= o_pos st')%Z /\ (od_plus_ok bs idxs 1 st' \/ od_dead (tokn idxs) st').

Lemma acc_arm_out : forall bs idxs st st', S1OUT bs idxs -> tokT bs idxs (tokn idxs - 1) = C_RBRACKET ->
  od_head_ok bs idxs 1 st -> acc bs idxs 1 st st' -> od_arm_out bs idxs st st'.
Proof.
  intros bs idxs st st' HS HLAST HH HA. split.
  - destruct HA as [| |j sbo' Hq Hc Hsb| |]; cbn [consume o_adv o_setd o_pos]; try lia.
    + unfold start_array. destruct (negb _); cbn [fst]; [lia|]. destruct (_ =? _)%Z; cbn [fst o_adv o_setd o_pos]; lia.
    + unfold start_object. destruct (negb _); [lia|]. destruct (_ =? _)%Z; cbn [o_adv o_setd o_pos]; lia.
  - left. eapply acc_plus_ok; eauto. lia.
Qed.

Ltac od_fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := step; od_fix_lit_store.

Lemma rw_cells_recell : forall segs (m : mem) A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] W' B' S'. split; [split|].
  - exact W'.
  - rewrite B'. exact Hb.
  - rewrite S'. exact Hw.
Qed.

Lemma rw_cells_C8_C4 : forall segs (m : mem) A pre v lo hi post,
  rw_cells segs m A (pre ++ C8 v :: post) -> le8 v = le4 lo ++ le4 hi ->
  rw_cells segs m A (pre ++ C4 lo :: C4 hi :: post).
Proof.
  intros segs m A pre v lo hi post H EQ. eapply rw_cells_recell; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. apply cells_wf_app. split; [exact W1|].
    cbn [cells_wf cell_wf] in *. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite EQ, <- app_assoc. reflexivity.
  - rewrite !cells_size_app. cbn [cells_size csize]. lia.
Qed.

Lemma od_le8_err_depth : le8 (Z_to_bv 64 4294967296) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 1).
Proof.
  rewrite <- store_bytes_8'. unfold le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  repeat (apply (f_equal2 (@cons byte)); [apply bv_eq; vm_compute; reflexivity|]). reflexivity.
Qed.

Lemma od_shl32_shr30 : forall x, (0 <= x < 4294967296)%Z -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = (4 * x)%Z.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z.
  replace (x * 4294967296)%Z with ((4 * x) * 1073741824)%Z by lia. apply Z.div_mul. lia.
Qed.

Lemma zx32_small : forall x, (0 <= x < 4294967296)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x H. unfold zx32. f_equal. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  apply Z.mod_small. change (2^32)%Z with 4294967296%Z. lia.
Qed.

Lemma od_signed_small : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2^64 / 2)%Z with (2^63)%Z.
  rewrite Zplus_mod_idemp_l.
  replace ((z + 2^63) mod 2^64)%Z with (z + 2^63)%Z by (symmetry; apply Z.mod_small; change (2^64)%Z with (2^63 + 2^63)%Z; lia). lia.
Qed.

Ltac odsig H := repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?x)] => rewrite (od_signed_small x) in H by lia
  end.

Lemma od_shl2 : forall x, Z.shiftl x 2 = (4 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2^2)%Z with 4%Z. lia. Qed.

Ltac odnorm :=
  unfold wz; s1norm;
  repeat match goal with
  | |- context [zx32 (Z_to_bv 64 ?x)] => rewrite (zx32_small x) by lia
  | |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by lia
  | |- context [Z.shiftl ?x 2] => rewrite (od_shl2 x)
  end.

Lemma wz_inj_small : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> wz a = wz b -> a = b.
Proof.
  intros a b Ha Hb H. apply (f_equal bv_unsigned) in H. unfold wz in H. rewrite !Z_to_bv_unsigned in H.
  rewrite !bv_wrap_small in H by (unfold bv_modulus; cbn; lia). exact H.
Qed.
