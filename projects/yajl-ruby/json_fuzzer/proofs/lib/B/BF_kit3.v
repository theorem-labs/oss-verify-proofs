(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ExecA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. aceil.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma rw_cells_reshape : forall segs m A cs cs',
  cells_wf cs' -> map bv_unsigned (cells_bytes cs') = map bv_unsigned (cells_bytes cs) -> rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. aceil.
  intros segs m A cs cs' WF EB0 [[WF0 BA] WR]. pose proof (bytes_eq_of_unsigned _ _ EB0) as EB.
  split; [split; [exact WF| rewrite EB; exact BA]|].
  rewrite <- (cells_bytes_length cs' WF), EB, (cells_bytes_length cs WF0). exact WR.
Qed.

Lemma rwc_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.
Lemma rwc_join : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. aceil.
  intros segs m A cs1 cs2 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length _ W1). auto.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))); [apply Wr; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Vr. lia.
Qed.
(* [comment removed for export] *)
Lemma rwc_join_at : forall segs m A A2 cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof. aceil. intros segs m A A2 cs1 cs2 H1 H2 ->. apply rwc_join; assumption. Qed.

Lemma k_bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof. aceil.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma k_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. aceil.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (k_bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. aceil.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (k_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
  rewrite <- HL. apply k_Z_to_le_bytes_to_Z.
Qed.

Lemma u64arr_of_cb : forall segs m A bs k,
  rw_cells segs m A [CB (8 * k) bs] -> exists ws, length ws = k /\ u64arr segs m A ws.
Proof. aceil.
  intros segs m A bs k [[WF Hb] Hw]. cbn in WF. destruct WF as [HL _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  assert (G : forall k bs, length bs = (8 * k)%nat -> exists ws, length ws = k /\ u64s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
    - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
      exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|].
      cbn [u64s]. rewrite Hu, le8_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (8 * Z.of_nat k)%Z with (Z.of_nat (8 * k)) by lia. exact Hw.
Qed.

Lemma cb_of_u64arr : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A [CB (8 * length ws) (u64s ws)].
Proof. aceil.
  intros segs m A ws [Hb Hw]. split; [split|].
  - cbn. rewrite u64s_length. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact Hw.
Qed.


(* [comment removed for export] *)
End RC__1.
Tactic Notation "leafA" uconstr(SPEC) :=
  eapply evtA_cut; [eapply SPEC|]; [..| cbv beta; let ms := fresh "ms'" in intros ms ->; ret_pc_lit].
