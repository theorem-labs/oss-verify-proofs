(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI06 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1d.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma afz_not_or : forall A B : Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof. intros A B H. split; intros X; apply H; [left | right]; exact X. Qed.
Lemma afz_land_low : forall u k j, 0 <= j -> 0 <= k < 2 ^ j -> Z.land u k = Z.land (u mod 2 ^ j) k.
Proof.
intros u k j Hj Hk. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
Qed.
Lemma afz_land_pow2_cases : forall v j, 0 <= v -> 0 <= j -> Z.land v (2 ^ j) = 0 \/ Z.land v (2 ^ j) = 2 ^ j.
Proof.
intros v j Hv Hj. pose proof (Z_land_upper v (2 ^ j) ltac:(lia)) as R.
assert (Hm : Z.land v (2 ^ j) mod 2 ^ j = 0).
{ rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
replace (Z.land (2 ^ j) (Z.ones j)) with 0; [apply Z.land_0_r|].
rewrite Z.land_ones by lia. symmetry. apply Z.mod_same. lia. }
pose proof (Z.pow_pos_nonneg 2 j ltac:(lia)) as P.
destruct (Z.eq_dec (Z.land v (2 ^ j)) 0) as [E|E]; [left; exact E | right].
pose proof (Z.div_mod (Z.land v (2 ^ j)) (2 ^ j) ltac:(lia)) as D. rewrite Hm in D.
assert (Hq : Z.land v (2 ^ j) / 2 ^ j = 1) by nia. lia.
Qed.
Section u.
Variables (E : env) (n : nat) (v : Z).
Hypothesis Hn : ew E n = Z_to_bv 64 v.
Hypothesis Hv : 0 <= v < 2 ^ 32.
Lemma afz_sext_land : forall k, 0 <= k < 2 ^ 32 -> U E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit k)) = Z.land v k.
Proof using Hn Hv.
intros k Hk. rewrite U_and_lit by lia. rewrite (afz_land_low _ k 32) by lia. rewrite (U_sext32_low E n v Hn Hv). reflexivity.
Qed.
Lemma afz_zext_sext : U E (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff n 0)) (SLit 32)) (SLit 32)) = v.
Proof using Hn Hv.
pose proof (U_sext32_low E n v Hn Hv) as Hl.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hz : zcanon (U E (SExt true 32 (SOff n 0)) * 2 ^ 32) = v * 2 ^ 32).
{ unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r by lia. rewrite Hl. reflexivity. }
rewrite Hz. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma afz_iff_sext : forall k, 0 <= k < 2 ^ 32 ->
U E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit k)) = 0 <-> Z.land v k = 0.
Proof using Hn Hv. intros k Hk. rewrite (afz_sext_land k Hk). tauto. Qed.
Lemma afz_iff_zext : forall k, 0 <= k < 2 ^ 32 ->
U E (SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff n 0)) (SLit 32)) (SLit 32)) (SLit k)) = 0 <-> Z.land v k = 0.
Proof using Hn Hv. intros k Hk. rewrite U_and_lit by lia. rewrite afz_zext_sext. tauto. Qed.
Lemma afz_U_bit2 : U E (SAlu ALU_SRL (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit 4)) (SLit 2)) = Z.land v 4 / 4.
Proof using Hn Hv.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (afz_sext_land 4) by lia. rewrite U_SLit. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. pose proof (Z_land_upper v 4 ltac:(lia)) as R.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ 1); [apply Z.div_le_upper_bound; lia | lia]].
Qed.
Lemma afz_iff_x1 :
U E (SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit 4)) (SLit 2)) (SLit 1)) = 0 <-> Z.land v 4 = 0.
Proof using Hn Hv.
rewrite U_and_lit by lia. rewrite afz_U_bit2.
destruct (afz_land_pow2_cases v 2 ltac:(lia) ltac:(lia)) as [E4|E4]; change (2 ^ 2) with 4 in E4; rewrite E4; vm_compute; split; intros; lia.
Qed.
Lemma afz_iff_b2 :
U E (SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_SLL (SExt false 8 (SOff n 0)) (SLit 62)) (SLit 63))
(SAlu ALU_SRL (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit 4)) (SLit 2))) = 0 <-> Z.land v 2 = 0 \/ Z.land v 4 = 0.
Proof using Hn Hv.
rewrite U_SAlu. cbn [zalu_raw]. rewrite afz_U_bit2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SExt, (U_atom E n v Hn) by lia. rewrite !U_SLit. change (Z.land (zcanon 62) 63) with 62. change (Z.land (zcanon 63) 63) with 63.
change (2 ^ Z.of_N 8) with 256. rewrite (zcanon_id (v mod 256)) by (unfold M64; pose proof (Z.mod_pos_bound v 256 ltac:(lia)); lia).
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hz : zcanon (v mod 256 * 2 ^ 62) = (v mod 4) * 2 ^ 62).
{ unfold zcanon, M64. change (2 ^ 64) with (4 * 2 ^ 62). rewrite Z.mul_mod_distr_r by lia.
f_equal. apply Z.mod_mod_divide. exists 64; reflexivity. }
rewrite Hz. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 63) with (2 ^ 62 * 2). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
rewrite (afz_land_low v 2 3) by lia. rewrite (afz_land_low v 4 3) by lia.
replace (v mod 4) with ((v mod 2 ^ 3) mod 4) by (apply Z.mod_mod_divide; exists 2; reflexivity).
pose proof (Z.mod_pos_bound v (2 ^ 3) ltac:(lia)) as R. generalize dependent (v mod 2 ^ 3). intros r Rr.
change (2 ^ 3) with 8 in Rr.
assert (Hr : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; split; intros; lia.
Qed.
End u.
Lemma afz_iff_atom : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
U E (SAlu ALU_AND (SOff n 0) (SLit k)) = 0 <-> Z.land v k = 0.
Proof. intros E n v k Hn Hv Hk. rewrite U_and_lit by lia. rewrite (U_atom E n v Hn Hv). tauto. Qed.
