(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1dj X1cr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j1 X0gi.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X173.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition wrap_malloc_entry : Z := 0x67f84.
Definition icpt_malloc_entry : Z := 0x68164.
Definition asan_malloc_entry : Z := 0x45b90.
Definition allocate_entry : Z := 0x45bec.
Definition wrap_free_entry : Z := 0x67f80.
Definition icpt_free_entry : Z := 0x67f94.
Definition asan_free_entry : Z := 0x458b0.
Definition deallocate_entry : Z := 0x458d8.
Definition qchunk_entry : Z := 0x49f18.
Definition qput_entry : Z := 0x4a090.
Definition run_malloc_hooks_entry : Z := 0x76884.
Definition run_free_hooks_entry : Z := 0x76940.
Definition gmcs_entry : Z := 0x70524.
Definition getpc_entry : Z := 0x890f8.
Definition lsan_disabled_entry : Z := 0x95c74.

Notation i_max_user := 1061496 (only parsing).
Notation i_min_rz := 1061504 (only parsing).

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
let bs := eval vm_compute in (option.default [] (image_bytes bsegs 0x105d8 8)) in
assert (RC1 : ro_cells bsegs mm 0x105d8 [CB (length bs) bs])
by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
let bs := eval vm_compute in (option.default [] (image_bytes bsegs 0x106b0 64)) in
assert (RC2 : ro_cells bsegs mm 0x106b0 [CB (length bs) bs])
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
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition wrap_malloc_entry : Z := 0x67e98.
Definition icpt_malloc_entry : Z := 0x68078.
Definition asan_malloc_entry : Z := 0x45aa4.
Definition allocate_entry : Z := 0x45b00.
Definition wrap_free_entry : Z := 0x67e94.
Definition icpt_free_entry : Z := 0x67ea8.
Definition asan_free_entry : Z := 0x457c4.
Definition deallocate_entry : Z := 0x457ec.
Definition qchunk_entry : Z := 0x49e2c.
Definition qput_entry : Z := 0x49fa4.
Definition run_malloc_hooks_entry : Z := 0x76798.
Definition run_free_hooks_entry : Z := 0x76854.
Definition gmcs_entry : Z := 0x70438.
Definition getpc_entry : Z := 0x8900c.
Definition lsan_disabled_entry : Z := 0x95b88.

Notation i_max_user := 1026616 (only parsing).
Notation i_min_rz := 1026624 (only parsing).

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
let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x105c0 8)) in
assert (RC1 : ro_cells asegs mm 0x105c0 [CB (length bs) bs])
by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x10698 64)) in
assert (RC2 : ro_cells asegs mm 0x10698 [CB (length bs) bs])
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
