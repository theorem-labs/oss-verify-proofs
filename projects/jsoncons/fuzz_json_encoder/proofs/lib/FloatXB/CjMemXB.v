(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Image SysStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s0 segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as <-. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. split; assumption.
  - destruct (IH a n seg H) as (Hin & B1 & B2). split; [right; exact Hin|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ro_addr_range_a : forall a, ro_addr ASEGS a = true -> (0x10000 <= bv_unsigned a < 0x15e000)%Z.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment ASEGS (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  destruct (find_segment_in _ _ _ _ E) as (Hin & B1 & B2).
  unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments in Hin.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold AsanUbsan_segment_000, AsanUbsan_segment_001,
           AsanUbsan_segment_002, AsanUbsan_segment_003 in *;
    cbn [seg_base seg_size seg_perms] in *.
  - lia.
  - lia.
  - vm_compute in H. discriminate.
  - vm_compute in H. discriminate.
Qed.

Lemma mem_inv_of_clear_a : forall M, L5.img_clear M 0x10000 0x15e000 -> mem_inv ASEGS M.
Proof.
  intros M C a b E. destruct (ro_addr ASEGS a) eqn:R; [|reflexivity]. exfalso.
  apply ro_addr_range_a in R. specialize (C (bv_unsigned a) R). rewrite Z_to_bv_bv_unsigned in C. congruence.
Qed.

(* [comment removed for export] *)
Definition ovl_bytes (M : word -> option byte) (a : Z) (n : nat) : list byte :=
  map (fun i => match M (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n).
Lemma ovl_bytes_length : forall M a n, length (ovl_bytes M a n) = n.
Proof. intros. unfold ovl_bytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma ovl_bytes_nth : forall M a n i, (i < n)%nat -> M (wa (a + Z.of_nat i)) <> None ->
  M (wa (a + Z.of_nat i)) = nth_error (ovl_bytes M a n) i.
Proof.
  intros M a n i Hi HD. unfold ovl_bytes. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map].
  rewrite Nat.add_0_l. destruct (M (wa (a + Z.of_nat i))) eqn:E; [reflexivity| contradiction].
Qed.

Lemma defined_rw_cells_g : forall segs M a n, L5.defined M a (Z.of_nat n) -> (0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
  rw_cells segs M a [CB n (ovl_bytes M a n)].
Proof.
  intros segs M a n HD H0 H1. split; [split|].
  - cbn. rewrite ovl_bytes_length. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. split; [rewrite ovl_bytes_length; exact H1|].
    intros i Hi. rewrite ovl_bytes_length in Hi. unfold mrd.
    assert (ND : M (wa (a + Z.of_nat i)) <> None) by (apply HD; lia).
    rewrite <- (ovl_bytes_nth M a n i Hi ND). destruct (M (wa (a + Z.of_nat i))); [reflexivity| contradiction].
  - split; [exact H0|]. split; [cbn; lia|]. intros i Hi. unfold wview.
    assert (ND : M (wa (a + i)) <> None) by (apply HD; cbn in Hi; lia).
    destruct (M (wa (a + i))); [discriminate| contradiction].
Qed.

Lemma stk_of_defined_g : forall segs M lo hi, L5.defined M lo (hi - lo) -> (0 <= lo)%Z -> (lo <= hi <= 2^64)%Z -> stk segs M lo hi.
Proof.
  intros segs M lo hi HD H0 H1. split; [exact H0|]. split; [lia|]. intros a Ha.
  assert (ND : M (wa a) <> None) by (replace a with (lo + (a - lo))%Z by lia; apply HD; lia).
  unfold wview, mrd. destruct (M (wa a)) as [b|]; [| contradiction]. split; [discriminate| exists b; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma wview_off_image_a : forall m a, (0x6c4000 <= bv_unsigned a)%Z -> wview ASEGS m a = m a.
Proof.
  intros m a H. unfold wview. destruct (m a); [reflexivity|].
  destruct (find_segment ASEGS (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. destruct (find_segment_in _ _ _ _ E) as (Hin & B1 & B2).
  unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments in Hin.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold AsanUbsan_segment_000, AsanUbsan_segment_001,
           AsanUbsan_segment_002, AsanUbsan_segment_003 in *;
    cbn [seg_base seg_size] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_L5_g : forall segs m a (o : list Z) rest, bytes_at segs m a (map (Z_to_bv 8) o ++ rest) -> L5.bytes_at segs m a o.
Proof.
  intros segs m a o rest (H0 & H1 & HB) i Hi. unfold L5.u8_at.
  assert (Hi' : (i < length (map (Z_to_bv 8) o ++ rest))%nat) by (rewrite length_app, length_map; lia).
  pose proof (HB i Hi') as E. rewrite nth_error_app1 in E by (rewrite length_map; lia).
  rewrite nth_error_map in E. rewrite (nth_error_nth' o 0%Z Hi) in E. cbn [option_map] in E.
  rewrite rdn_unfold. change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)). rewrite E.
  rewrite rdn_unfold. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munch2_frame_but_g : forall lo1 hi1 lo2 hi2 m m',
  munch [(lo1, hi1); (lo2, hi2)]%Z m m' -> L5.frame_but [(lo1, hi1 - lo1); (lo2, hi2 - lo2)]%Z m m'.
Proof.
  intros lo1 hi1 lo2 hi2 m m' MU x Hx. apply MU. cbn [outside].
  unfold L5.outside, L5.in_rng in Hx. cbn [fst snd] in Hx.
  split; [intros C; apply (Hx (lo1, hi1 - lo1)%Z); [left; reflexivity| cbn; lia]|].
  split; [intros C; apply (Hx (lo2, hi2 - lo2)%Z); [right; left; reflexivity| cbn; lia]| exact I].
Qed.

(* [comment removed for export] *)
Lemma fmt_bytes_at_a : forall m A f, mem_inv ASEGS m -> ro_bytes_b ASEGS A (map (Z_to_bv 8) f) = true -> 0 <= A -> A + Z.of_nat (length f) <= 2^64 ->
  bytes_at ASEGS m A (map (Z_to_bv 8) f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at ASEGS m A _ (ro_cells_image ASEGS m A (map (Z_to_bv 8) f) MI RB H0 ltac:(rewrite length_map; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma got_slot_rom_a : forall i, (i < 8)%nat -> seg_rom ASEGS (wa (0x1652e0 + Z.of_nat i)) = nth_error (le8 (Z_to_bv 64 0x6c18d0)) i.
Proof. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; f_equal; apply bv_eq; reflexivity|]). lia. Qed.
Lemma got_slot_wview_a : forall M i, (i < 8)%nat -> M (wa (0x1652e0 + Z.of_nat i)) = None -> wview ASEGS M (wa (0x1652e0 + Z.of_nat i)) <> None.
Proof. intros M i Hi E. unfold wview. rewrite E. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma guard_rom_a : forall i, (i < 8)%nat -> seg_rom ASEGS (wa (0x6c18d0 + Z.of_nat i)) <> None.
Proof. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma guard_wview_a : forall M i, (i < 8)%nat -> wview ASEGS M (wa (0x6c18d0 + Z.of_nat i)) <> None.
Proof.
  intros M i Hi. unfold wview. destruct (M (wa (0x6c18d0 + Z.of_nat i))); [discriminate|].
  do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia.
Qed.

Definition guard_bytes_a (M : word -> option byte) : list byte :=
  map (fun i => match mrd ASEGS M (wa (0x6c18d0 + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 8).
Lemma guard_bytes_a_length : forall M, length (guard_bytes_a M) = 8%nat.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons_a : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_to_Z_a : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons_a.
  pose proof (u8_range b) as Hb. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

Lemma le8_of_bytes_a : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as HR. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z_a.
Qed.

(* [comment removed for export] *)
Lemma ssp_cells_a : forall M, L5.img_clear M 0x10000 0x166000 ->
  rw_cells ASEGS M 0x1652e0 [C8 (Z_to_bv 64 0x6c18d0)] /\ rw_cells ASEGS M 0x6c18d0 [C8 (le_bytes_to_word (guard_bytes_a M))].
Proof.
  intros M C. split.
  - split; [split|].
    + cbn. tauto.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_le8; lia|].
      intros i Hi. rewrite length_le8 in Hi. unfold mrd.
      pose proof (C (0x1652e0 + Z.of_nat i)%Z ltac:(lia)) as Ci. change (Z_to_bv 64 (0x1652e0 + Z.of_nat i)) with (wa (0x1652e0 + Z.of_nat i)) in Ci.
      rewrite Ci. apply got_slot_rom_a. exact Hi.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. apply got_slot_wview_a; [lia|].
      pose proof (C (0x1652e0 + Z.of_nat (Z.to_nat i))%Z ltac:(lia)) as Ci. exact Ci.
  - split; [split|].
    + cbn. tauto.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite le8_of_bytes_a by apply guard_bytes_a_length.
      split; [lia|]. split; [rewrite guard_bytes_a_length; lia|].
      intros i Hi. rewrite guard_bytes_a_length in Hi. unfold guard_bytes_a. rewrite nth_error_map.
      rewrite (nth_error_nth' (seq 0 8) 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map]. rewrite Nat.add_0_l.
      destruct (mrd ASEGS M (wa (0x6c18d0 + Z.of_nat i))) eqn:E; [first [reflexivity | exact E]|].
      exfalso. unfold mrd in E. destruct (M (wa (0x6c18d0 + Z.of_nat i))); [discriminate|]. exact (guard_rom_a i Hi E).
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. apply guard_wview_a. lia.
Qed.
