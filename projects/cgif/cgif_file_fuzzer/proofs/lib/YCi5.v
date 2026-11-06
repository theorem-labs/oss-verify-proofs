(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YI04 YI09 YI08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma land_shr2_2 : forall Y a : Z, 0 <= Y -> 0 <= a -> Y mod 2 ^ 32 = a mod 2 ^ 32 -> Z.land (Z.shiftr Y 2) 2 = Z.land (Z.shiftr a 2) 2.
Proof.
intros Y a HY Ha Hm. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z.eq_dec n 1) as [-> | Hne].
- change (1 + 2) with 3. rewrite <- (Z.mod_pow2_bits_low Y 32 3), <- (Z.mod_pow2_bits_low a 32 3), Hm by lia. reflexivity.
- replace (Z.testbit 2 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
symmetry. destruct (Z.eq_dec n 0) as [-> | Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia.
assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma land_shr2_2_cases : forall a, Z.land (Z.shiftr a 2) 2 = 0 \/ Z.land (Z.shiftr a 2) 2 = 2.
Proof.
intros a. destruct (Z.testbit (Z.shiftr a 2) 1) eqn:Eb.
- right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. destruct (Z.eq_dec n 1) as [->|Hne]; [rewrite Eb; reflexivity|].
replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
- left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec n 1) as [->|Hne]; [rewrite Eb; reflexivity|].
replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma U_rattrX : forall E (na nt : nat) a t, ew E na = Z_to_bv 64 a -> 0 <= a < 2 ^ 32 -> ew E nt = Z_to_bv 64 t -> (t = 0 \/ t = 1) ->
U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SRL (SExt true 32 (SOff na 0)) (SLit 2)) (SLit 2)) (SOff nt 0)) mod 2 ^ 32 = Z.lor (Z.land (Z.shiftr a 2) 2) t.
Proof.
intros E na nt a t H64 Ha H10 Ht.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SExt. cbn [Z.of_N]. rewrite (U_atom _ na a H64) by lia. rewrite (U_atom _ nt t H10) by lia. rewrite !U_SLit.
change (zcanon 2) with 2. change (Z.land 2 63) with 2. rewrite (Z.mod_small a) by lia.
set (Y := zcanon (bv_swrap 32 a)).
assert (HY : 0 <= Y < 2 ^ 64) by (subst Y; apply zcanon_range).
assert (HYm : Y mod 2 ^ 32 = a mod 2 ^ 32).
{ subst Y. rewrite zcanon_wrap. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
replace (a + 2 ^ 31 - 2 ^ 31) with a by lia. reflexivity. }
assert (HM64 : M64 = 2 ^ 64) by reflexivity.
rewrite (zcanon_id (Z.shiftr Y 2)) by (rewrite HM64; split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia]).
rewrite (land_shr2_2 Y a) by (try lia; rewrite HYm, Z.mod_small by lia; reflexivity).
pose proof (land_shr2_2_cases a) as Hl2.
assert (Hor : 0 <= Z.lor (Z.land (Z.shiftr a 2) 2) t < 4).
{ clear - Hl2 Ht. destruct Hl2 as [E2|E2]; rewrite E2; destruct Ht as [E1|E1]; rewrite E1;
match goal with |- 0 <= ?x < 4 => let v := eval vm_compute in x in change x with v end; lia. }
rewrite (zcanon_id (Z.land (Z.shiftr a 2) 2)) by (rewrite HM64; clear - Hl2; lia).
rewrite zcanon_id by (rewrite HM64; clear - Hor; lia). apply Z.mod_small. clear - Hor; lia.
Qed.
Lemma rattr_model : forall a t, (t = 0 \/ t = 1) ->
Z.lor (Z.land (Z.shiftr a 2) 2) t = t + (if YO07.flag a 8 then 2 else 0).
Proof.
intros a t Ht. unfold YO07.flag.
assert (H8 : Z.land a 8 = 0 <-> Z.land (Z.shiftr a 2) 2 = 0).
{ split; intros H; apply Z.bits_inj'; intros n Hn; rewrite Z.bits_0, Z.land_spec.
- rewrite Z.shiftr_spec by lia. destruct (Z.eq_dec n 1) as [->|Hne].
+ apply (f_equal (fun z => Z.testbit z 3)) in H. rewrite Z.bits_0, Z.land_spec in H. change (Z.testbit 8 3) with true in H. rewrite Bool.andb_true_r in H.
change (1 + 2) with 3. rewrite H. reflexivity.
+ replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
- destruct (Z.eq_dec n 3) as [->|Hne].
+ apply (f_equal (fun z => Z.testbit z 1)) in H. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec in H by lia. change (Z.testbit 2 1) with true in H.
rewrite Bool.andb_true_r in H. change (1 + 2) with 3 in H. rewrite H. reflexivity.
+ replace (Z.testbit 8 n) with false; [apply Bool.andb_false_r|]. symmetry.
destruct (Z.lt_ge_cases n 3) as [Hlt|Hge].
* destruct (Z.eq_dec n 0) as [->|H0]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|H1]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|H2]; [reflexivity|]. lia.
* rewrite (Z.testbit_false 8 n) by lia. assert (8 < 2 ^ n) by (change 8 with (2 ^ 3); apply Z.pow_lt_mono_r; lia). rewrite Z.div_small by lia. reflexivity. }
pose proof (land_shr2_2_cases a) as [E2|E2]; rewrite E2.
- destruct (Z.eqb_spec (Z.land a 8) 0) as [E8|E8]; [| exfalso; apply E8; apply H8; exact E2]. cbn. destruct Ht as [->| ->]; reflexivity.
- destruct (Z.eqb_spec (Z.land a 8) 0) as [E8|E8]; [exfalso; pose proof (proj1 H8 E8); lia|]. cbn. destruct Ht as [->| ->]; reflexivity.
Qed.
Lemma U_sext16_field : forall E n d, ew E n = Z_to_bv 64 d -> 0 <= d < 2 ^ (8 * 2) -> U E (SExt true 16 (SOff n 0)) mod 2 ^ 16 = d.
Proof.
intros E n d Hn Hd.
rewrite U_SExt. cbn [Z.of_N]. rewrite (U_atom _ n d Hn) by lia.
rewrite (Z.mod_small d) by lia. rewrite zcanon_wrap.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 16) with (2 ^ 16). change (bv_half_modulus 16) with (2 ^ 15).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 16)) by (exists (2 ^ 48); reflexivity).
rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
replace (d + 2 ^ 15 - 2 ^ 15) with d by lia. apply Z.mod_small. lia.
Qed.
