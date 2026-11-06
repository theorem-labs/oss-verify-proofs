(* LLVMFuzzerTestOneInput_segX_up_den: the values of the symbolic expressions the Pa engine builds for the image-B
   `up` segment's in-line channel-count check (+0x844..+0x8a0 of LLVMFuzzerTestOneInput), and the refutation of the
   abort edge +0x8a0 (`bne s5, a0, +0xb88`) on each of the four paths that reach it.

   The expressions are the engine's own (read off its states at +0x874, +0x880 and +0x8a0): q is the quotient of
   +0x85c / +0x860, rem the remainder of +0x86c, qm2 the `addiw a2, a1, -2` of +0x878, and a0 the in-line count of
   +0x884..+0x89c. Atom 22 is s6 = len and atom 10 is a0 at +0x840 = reac_upstream_channels' return. The arithmetic
   is lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_arith.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_c
  LLVMFuzzerTestOneInput_segX_up_arith.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition up_sq : sv := SAlu ALU_SRL (SMd M_MULHU (SOff 22 (-52)) (SLit 16397105843297379215)) (SLit 5).
Definition up_srem : sv := SAlu ALU_SUB (SOff 22 (-52)) (SMd M_MUL up_sq (SLit 36)).
Definition up_sqm2 : sv := SAluw ALU_ADD up_sq (SLit (-2)).
Definition up_sa0 : sv :=
  SAluw ALU_ADD (SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_AND up_sq (SLit 1)) (SLit 1)) (SLit (-1))) up_sq)
    (SLit 0).

Lemma up_M64 : M64 = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma up_zcanon_small : forall z, 0 <= z < 18446744073709551616 -> zcanon z = z.
Proof. intros z Hz. apply zcanon_id. rewrite up_M64. exact Hz. Qed.

Lemma up_lor_ones : forall q, 0 <= q < 18446744073709551616 -> Z.lor 18446744073709551615 q = 18446744073709551615.
Proof.
intros q Hq. change 18446744073709551615 with (Z.ones 64).
destruct (Z.eq_dec q 0) as [->|Hq0]; [rewrite Z.lor_0_r; reflexivity|].
rewrite Z.lor_comm. apply Z.lor_ones_low; [lia|].
apply Z.log2_lt_pow2; [lia|]. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Section den.
Variable E : env.
Variable len : Z.
Hypothesis E22 : ew E 22 = Z_to_bv 64 len.
Hypothesis Hlen : 0 <= len < UP_NMAX.

Lemma up_U22 : U E (SOff 22 0) = len.
Proof.
rewrite U_SOff, E22, Z.add_0_r. unfold UP_NMAX in Hlen.
rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
apply up_zcanon_small. lia.
Qed.

Section ge52.
Hypothesis H52 : 52 <= len.

Lemma up_U_off52 : U E (SOff 22 (-52)) = len - 52.
Proof.
rewrite U_SOff, E22. unfold UP_NMAX in Hlen.
rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
apply up_zcanon_small. lia.
Qed.

Lemma up_U_sq : U E up_sq = (len - 52) / 36.
Proof.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
unfold up_sq. rewrite U_SAlu, U_SMd, up_U_off52, !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (up_zcanon_small 16397105843297379215) by lia.
rewrite (up_zcanon_small 5) by lia. change (Z.land 5 63) with 5. change (Z.of_N 64) with 64.
assert (Hx : 0 <= (len - 52) * 16397105843297379215 / 2 ^ 64 < 18446744073709551616).
{ split; [apply Z.div_pos; [unfold UP_NMAX in Hlen; nia | reflexivity]|].
  apply Z.div_lt_upper_bound; [reflexivity|]. unfold UP_NMAX in Hlen. change (2 ^ 64) with 18446744073709551616. nia. }
rewrite (Z.shiftr_div_pow2 ((len - 52) * 16397105843297379215) 64) by lia.
rewrite (up_zcanon_small ((len - 52) * 16397105843297379215 / 2 ^ 64)) by exact Hx.
rewrite (Z.shiftr_div_pow2 ((len - 52) * 16397105843297379215 / 2 ^ 64) 5) by lia. change (2 ^ 5) with 32.
pose proof (up_mulsh_eq (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hm. unfold up_mulsh in Hm.
unfold UPSTREAM_DIV36 in Hm. rewrite Hm.
apply up_zcanon_small. lia.
Qed.

Lemma up_U_srem : U E up_srem = (len - 52) mod 36.
Proof.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
pose proof (Z.div_mod (len - 52) 36 ltac:(discriminate)) as Hd.
pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as Hr.
unfold up_srem. rewrite U_SAlu, U_SMd, up_U_off52, up_U_sq, U_SLit. cbn [zalu_raw zmd_raw].
rewrite (up_zcanon_small 36) by lia.
rewrite (up_zcanon_small ((len - 52) / 36 * 36)) by lia.
rewrite up_zcanon_small by lia. lia.
Qed.

(* bv_swrap 32 on a value whose low 32 bits read as a small signed number. *)
Lemma up_swrap32 : forall z s, -2147483648 <= s < 2147483648 -> z = s + 4294967296 * ((z - s) / 4294967296) ->
  bv_swrap 32 z = s.
Proof.
intros z s Hs Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
change (bv_modulus 32) with 4294967296.
rewrite Hz. replace (s + 4294967296 * ((z - s) / 4294967296) + 2147483648)
  with ((s + 2147483648) + ((z - s) / 4294967296) * 4294967296) by ring.
rewrite Z.mod_add by discriminate. rewrite Z.mod_small by lia. ring.
Qed.

Lemma up_wrap64 : forall z, bv_wrap 64 z = z mod 18446744073709551616.
Proof. intros z. reflexivity. Qed.

Lemma up_U_sqm2 : U E up_sqm2 = ((len - 52) / 36 - 2) mod 18446744073709551616.
Proof.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
set (q := (len - 52) / 36) in *.
unfold up_sqm2. rewrite U_of_S, S_SAluw, up_U_sq, U_SLit. fold q. cbn [zalu_raw].
change (zcanon (-2)) with 18446744073709551614.
change (2 ^ 32) with 4294967296. change (18446744073709551614 mod 4294967296) with 4294967294.
rewrite (Z.mod_small q 4294967296) by lia.
rewrite (up_swrap32 (q + 4294967294) (q - 2)); [apply up_wrap64 | lia |].
replace (q + 4294967294 - (q - 2)) with (1 * 4294967296) by ring.
rewrite Z.div_mul by discriminate. ring.
Qed.

Lemma up_U_sa0 : U E up_sa0 = (if Z.even ((len - 52) / 36) then (len - 52) / 36 else -1) mod 18446744073709551616.
Proof.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
pose proof (up_U_sq) as Uq.
set (q := (len - 52) / 36) in *.
assert (UW : U E (SAlu ALU_AND up_sq (SLit 1)) = q mod 2).
{ rewrite U_SAlu, Uq, U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
  rewrite up_land1_mod2 by lia. apply up_zcanon_small. pose proof (Z.mod_pos_bound q 2); lia. }
assert (UZ : U E (SAlu ALU_SLTU (SAlu ALU_AND up_sq (SLit 1)) (SLit 1)) = if q mod 2 =? 0 then 1 else 0).
{ rewrite U_SAlu, UW, U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
  pose proof (Z.mod_pos_bound q 2).
  destruct (Z.eqb_spec (q mod 2) 0) as [H0|H0].
  - rewrite H0. reflexivity.
  - replace (q mod 2) with 1 by lia. reflexivity. }
assert (UY : U E (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_AND up_sq (SLit 1)) (SLit 1)) (SLit (-1))) =
             if q mod 2 =? 0 then 0 else 18446744073709551615).
{ rewrite U_SAlu, UZ, U_SLit. cbn [zalu_raw]. change (zcanon (-1)) with 18446744073709551615.
  destruct (q mod 2 =? 0); vm_compute; reflexivity. }
assert (UX : U E (SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_AND up_sq (SLit 1)) (SLit 1)) (SLit (-1)))
                    up_sq) = if q mod 2 =? 0 then q else 18446744073709551615).
{ rewrite U_SAlu, UY, Uq. cbn [zalu_raw]. destruct (q mod 2 =? 0).
  - rewrite Z.lor_0_l. apply up_zcanon_small. lia.
  - rewrite up_lor_ones by lia. reflexivity. }
unfold up_sa0. rewrite U_of_S, S_SAluw, UX, U_SLit. change (zcanon 0) with 0.
rewrite <- up_mod2_even. change (2 ^ 32) with 4294967296. rewrite Zmod_0_l, Z.add_0_r.
destruct (q mod 2 =? 0).
- rewrite (Z.mod_small q 4294967296) by lia.
  rewrite (up_swrap32 q q); [apply up_wrap64 | lia |].
  replace (q - q) with 0 by ring. rewrite Zdiv_0_l. ring.
- vm_compute. reflexivity.
Qed.
End ge52.

(* s5 = a0 at +0x840 = reac_upstream_channels' return. *)
Hypothesis E10 : ew E 10 = Z_to_bv 64 (upstream_result len).

Lemma up_U10 : U E (SOff 10 0) = upstream_result len mod 18446744073709551616.
Proof.
rewrite U_SOff, E10, Z.add_0_r. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
unfold zcanon. rewrite up_M64. apply Z.mod_mod. discriminate.
Qed.

Lemma up_res_m1 : upstream_result len = -1 -> U E (SOff 10 0) = U E (SLit 18446744073709551615).
Proof. intros H. rewrite up_U10, H, U_SLit. reflexivity. Qed.

(* +0x8a0 on the path len < 52 (the `bltu s6, a1` of +0x84c taken). *)
Lemma up_abort_lt52 :
  branch_taken BC_LTU (sv_denot E (SOff 22 0)) (sv_denot E (SLit 52)) = true ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 18446744073709551615)) = false.
Proof.
intros Hc. rewrite branch_ltu_U, up_U22, U_SLit in Hc. change (zcanon 52) with 52 in Hc. apply Z.ltb_lt in Hc.
rewrite branch_ne_U, up_res_m1; [rewrite Z.eqb_refl; reflexivity|].
unfold upstream_result, upstream_ok.
replace (52 <=? len) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* +0x8a0 on the path 52 <= len, remainder not zero (the `bne a2, zero` of +0x874 taken). *)
Lemma up_abort_rem :
  branch_taken BC_LTU (sv_denot E (SOff 22 0)) (sv_denot E (SLit 52)) = false ->
  branch_taken BC_NE (sv_denot E up_srem) (sv_denot E (SLit 0)) = true ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 18446744073709551615)) = false.
Proof.
intros Hc0 Hc. rewrite branch_ltu_U, up_U22, U_SLit in Hc0. change (zcanon 52) with 52 in Hc0. apply Z.ltb_ge in Hc0.
rewrite branch_ne_U, up_U_srem, U_SLit in Hc by exact Hc0. change (zcanon 0) with 0 in Hc.
rewrite branch_ne_U, up_res_m1; [rewrite Z.eqb_refl; reflexivity|].
unfold upstream_result, upstream_ok.
replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
destruct ((len - 52) mod 36 =? 0); [discriminate | reflexivity].
Qed.

(* +0x8a0 on the path remainder zero, quotient outside [2, 40] (the `bltu a3, a2` of +0x880 taken). *)
Lemma up_abort_range :
  branch_taken BC_LTU (sv_denot E (SOff 22 0)) (sv_denot E (SLit 52)) = false ->
  branch_taken BC_LTU (sv_denot E (SLit 38)) (sv_denot E up_sqm2) = true ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 18446744073709551615)) = false.
Proof.
intros Hc0 Hc. rewrite branch_ltu_U, up_U22, U_SLit in Hc0. change (zcanon 52) with 52 in Hc0. apply Z.ltb_ge in Hc0.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
rewrite branch_ltu_U, U_SLit, up_U_sqm2 in Hc by exact Hc0. change (zcanon 38) with 38 in Hc.
apply Z.ltb_lt in Hc.
assert (Hr : ((2 <=? (len - 52) / 36) && ((len - 52) / 36 <=? 40))%bool = false).
{ rewrite <- (up_range_test _ Hq). unfold UP_P64. apply Z.leb_gt. exact Hc. }
rewrite branch_ne_U, up_res_m1; [rewrite Z.eqb_refl; reflexivity|].
unfold upstream_result, upstream_ok. rewrite (up_width_small len Hlen Hc0).
apply andb_false_iff in Hr as [Hr | Hr];
  [rewrite Hr; rewrite !Bool.andb_false_r; reflexivity
  | rewrite Hr; rewrite Bool.andb_false_r; reflexivity].
Qed.

(* +0x8a0 on the path that computes the count (the `bltu a3, a2` of +0x880 not taken). *)
Lemma up_abort_count :
  branch_taken BC_LTU (sv_denot E (SOff 22 0)) (sv_denot E (SLit 52)) = false ->
  branch_taken BC_NE (sv_denot E up_srem) (sv_denot E (SLit 0)) = false ->
  branch_taken BC_LTU (sv_denot E (SLit 38)) (sv_denot E up_sqm2) = false ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E up_sa0) = false.
Proof.
intros Hc0 Hc1 Hc. rewrite branch_ltu_U, up_U22, U_SLit in Hc0. change (zcanon 52) with 52 in Hc0. apply Z.ltb_ge in Hc0.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
rewrite branch_ne_U, up_U_srem, U_SLit in Hc1 by exact Hc0. change (zcanon 0) with 0 in Hc1.
apply Bool.negb_false_iff, Z.eqb_eq in Hc1.
rewrite branch_ltu_U, U_SLit, up_U_sqm2 in Hc by exact Hc0. change (zcanon 38) with 38 in Hc.
apply Z.ltb_ge in Hc.
assert (Hr : ((2 <=? (len - 52) / 36) && ((len - 52) / 36 <=? 40))%bool = true).
{ rewrite <- (up_range_test _ Hq). unfold UP_P64. apply Z.leb_le. exact Hc. }
apply andb_prop in Hr as [H2 H40]. apply Z.leb_le in H2. apply Z.leb_le in H40.
rewrite branch_ne_U, up_U10, up_U_sa0 by exact Hc0.
unfold upstream_result, upstream_ok. rewrite (up_width_small len Hlen Hc0).
replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
rewrite Hc1. cbn [Z.eqb andb].
replace (2 <=? (len - 52) / 36) with true by (symmetry; apply Z.leb_le; lia).
replace ((len - 52) / 36 <=? 40) with true by (symmetry; apply Z.leb_le; lia).
rewrite !Bool.andb_true_r. destruct (Z.even ((len - 52) / 36)); rewrite Z.eqb_refl; reflexivity.
Qed.
End den.

(* +0x8a4..+0x8c0: the upstream buffer's size. `blt zero, s5` (+0x8a4) on the count r (atom 21), then on the taken
   arm `li a0, 36; mul a0, s5, a0; sltiu a1, a0, 1; or s8, a0, a1` and `mv a0, s8` (+0x8b0..+0x8c0): the engine's
   expressions at the malloc call. *)
Definition up_s36 : sv := SMd M_MUL (SOff 21 0) (SLit 36).
Definition up_s8 : sv := SAlu ALU_OR up_s36 (SAlu ALU_SLTU up_s36 (SLit 1)).
Definition up_sa0b : sv := SAlu ALU_ADD up_s8 (SLit 0).

Section olen.
Variable E : env.
Variable r : Z.
Hypothesis E21 : ew E 21 = Z_to_bv 64 r.

Lemma up_lt0_s5 : -1 <= r <= 40 ->
  branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff 21 0)) = (0 <? r).
Proof.
intros Hr. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
change (bv_signed (sv_denot E (SOff 21 0))) with (Sg E (SOff 21 0)).
rewrite S_SLit, S_SOff, E21, Z.add_0_r, Z_to_bv_unsigned.
assert (Hs : forall z, -9223372036854775808 <= z < 9223372036854775808 -> bv_swrap 64 (bv_wrap 64 z) = z).
{ intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808.
  change (bv_modulus 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by discriminate.
  rewrite Z.mod_small by lia. ring. }
rewrite (Hs r) by lia. change (bv_swrap 64 0) with 0. reflexivity.
Qed.

Lemma up_U_s36 : 0 < r <= 40 -> U E up_s36 = 36 * r.
Proof.
intros Hr. unfold up_s36. rewrite U_SMd, U_SOff, U_SLit, E21, Z.add_0_r. cbn [zmd_raw].
rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite (up_zcanon_small r) by lia. change (zcanon 36) with 36.
rewrite Z.mul_comm. apply up_zcanon_small. lia.
Qed.

Lemma up_U_s8 : 0 < r <= 40 -> U E up_s8 = 36 * r.
Proof.
intros Hr. unfold up_s8. rewrite U_SAlu, U_SAlu, up_U_s36 by exact Hr. rewrite U_SLit. cbn [zalu_raw].
change (zcanon 1) with 1. replace (36 * r <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
change (zcanon 0) with 0. rewrite Z.lor_0_r. apply up_zcanon_small. lia.
Qed.

Lemma up_U_sa0b : 0 < r <= 40 -> U E up_sa0b = 36 * r.
Proof.
intros Hr. unfold up_sa0b. rewrite U_SAlu, up_U_s8 by exact Hr. rewrite U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. rewrite Z.add_0_r. apply up_zcanon_small. lia.
Qed.
End olen.

(* The count is -1 or in [2, 40]. *)
Lemma up_result_range : forall len, 0 <= len < UP_NMAX -> -1 <= upstream_result len <= 40.
Proof.
intros len Hlen. destruct (up_result_cases len Hlen) as [H | (H & H2 & _)]; rewrite H; lia.
Qed.
