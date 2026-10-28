(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition wrap_malloc_entry : Z := 0x82e7c.
Definition icpt_malloc_entry : Z := 0x83058.
Definition asan_malloc_entry : Z := 0x5b60c.
Definition allocate_entry : Z := 0x5b668.
Definition wrap_free_entry : Z := 0x82e78.
Definition icpt_free_entry : Z := 0x82e88.
Definition asan_free_entry : Z := 0x5b32c.
Definition deallocate_entry : Z := 0x5b354.
Definition qchunk_entry : Z := 0x5f8b4.
Definition qput_entry : Z := 0x5fa2c.
Definition run_malloc_hooks_entry : Z := 0x9171c.
Definition run_free_hooks_entry : Z := 0x917d8.
Definition gmcs_entry : Z := 0x8b4d0.
Definition getpc_entry : Z := 0xa3fac.
Definition lsan_disabled_entry : Z := 0xb0b28.

Notation i_max_user := 1512440 (only parsing).
Notation i_min_rz := 1512448 (only parsing).

Definition needed2 (n : Z) : Z := needed n + (if from_primary n then 0 else rz_size n).

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048.
Proof.
  intros n. unfold rz_size. pose proof (rz_log_range n) as R.
  assert (C : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6
              \/ rz_log n = 7) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn; lia.
Qed.

Lemma rounded_range : forall n, 1 <= n -> n <= rounded n <= n + 7 /\ 8 <= rounded n /\ rounded n mod 8 = 0.
Proof.
  intros n Hn. unfold rounded. rewrite (Z.max_l n 1) by lia.
  destruct (Z.le_gt_cases n 8) as [L|L].
  - rewrite Z.max_r by lia. cbn. lia.
  - rewrite Z.max_l by lia. split; [| split]; [| | rewrite Z.mul_comm; apply Z.mod_mul; lia].
    + pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia.
    + pose proof (Z.div_le_mono 16 (n + 7) 8 ltac:(lia) ltac:(lia)). cbn in H. lia.
Qed.

Lemma needed2_range : forall n, 1 <= n <= 2^31 -> 24 <= needed2 n <= n + 7 + 4096 /\ needed2 n mod 8 = 0.
Proof.
  intros n Hn. unfold needed2, needed. pose proof (rounded_range n ltac:(lia)) as (R1 & R2 & R3).
  pose proof (rz_size_range n) as RZ.
  assert (RZ8 : rz_size n mod 8 = 0).
  { unfold rz_size. pose proof (rz_log_range n) as R.
    assert (C : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6
                \/ rz_log n = 7) by lia.
    destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. }
  destruct (from_primary n); split; try lia; Z.div_mod_to_equations; lia.
Qed.

Ltac amem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Ltac ro_debruijn MI :=
  let mm := amem in
  let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x10450 8)) in
  assert (RC1 : ro_cells asegs mm 0x10450 [CB (length bs) bs])
    by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
  let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x104c8 64)) in
  assert (RC2 : ro_cells asegs mm 0x104c8 [CB (length bs) bs])
    by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
  cbn [length] in RC1, RC2.

Ltac fold_reg k := let e := getreg k in lazymatch e with Z_to_bv 64 ?x => let v := eval vm_compute in x in change x with v end.

Lemma land_m8 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  intros x Hx.
  assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  assert (E2 : Z.ones 64 = Z.lor 18446744073709551608 7) by reflexivity.
  rewrite E2, Z.land_lor_distr_r in E1.
  pose proof (Z.add_lor_land (Z.land x 18446744073709551608) (Z.land x 7)) as E3.
  assert (E4 : Z.land (Z.land x 18446744073709551608) (Z.land x 7) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
    assert (B : Z.testbit 18446744073709551608 i && Z.testbit 7 i = false)
      by (rewrite <- Z.land_spec; change (Z.land 18446744073709551608 7) with 0; apply Z.bits_0).
    destruct (Z.testbit x i), (Z.testbit 18446744073709551608 i), (Z.testbit 7 i); cbn in *; congruence. }
  rewrite E4, Z.add_0_r, E1 in E3.
  change 7 with (Z.ones 3) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 3) with 8 in E3.
  pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Lemma rounded_machine : forall n, 1 <= n <= 2 ^ 31 ->
  Z.land (Z.max n 8 + 7) (Z.land (0 + - (8)) 18446744073709551615) + Z.land (Z.land (Z.b2z (8 <? 9) + -1) 18446744073709551615) 8
  = rounded n.
Proof.
  intros n Hn. change (Z.land (0 + - (8)) 18446744073709551615) with 18446744073709551608.
  change (Z.land (Z.land (Z.b2z (8 <? 9) + -1) 18446744073709551615) 8) with 0.
  rewrite land_m8 by lia. unfold rounded. rewrite (Z.max_l n 1) by lia. lia.
Qed.

Lemma rz_size_mod16 : forall n, rz_size n mod 16 = 0.
Proof.
  intros n. unfold rz_size. pose proof (rz_log_range n) as R.
  assert (C : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6
              \/ rz_log n = 7) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
Qed.

Lemma land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma needed2_ge : forall n, 1 <= n -> n + rz_size n <= needed2 n.
Proof.
  intros n Hn. unfold needed2, needed. pose proof (rounded_range n Hn) as (R1 & _ & _). pose proof (rz_size_range n).
  destruct (from_primary n); lia.
Qed.

Lemma le1_any : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.

Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_any z); mem_after_store
  end.
