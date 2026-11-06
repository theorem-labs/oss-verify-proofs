(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI02 YI01 YI03 YI07 YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac perm_norm :=
repeat match goal with
| |- context [?x :: ?l] => lazymatch l with nil => fail | _ => change (x :: l) with ([x] ++ l) end
end;
repeat rewrite <- app_assoc; rewrite ?app_nil_l.
Ltac perm_front c :=
lazymatch goal with
| |- Permutation (c ++ ?t) _ => apply Permutation_refl
| |- Permutation c _ => rewrite <- (app_nil_r c) at 1; apply Permutation_refl
| |- Permutation (?d ++ ?t) _ =>
eapply (@Permutation_trans _ (d ++ t) (d ++ (c ++ _)) (c ++ _));
[ apply Permutation_app_head; perm_front c | apply Permutation_app_swap_app ]
end.
Ltac perm_tac :=
perm_norm;
repeat (lazymatch goal with
| |- Permutation ?l ?l => apply Permutation_refl
| |- Permutation (?c ++ ?l) ?R =>
eapply (@Permutation_trans _ (c ++ l) (c ++ _) R); [ apply Permutation_app_head | apply Permutation_sym; perm_front c ]
| |- Permutation ?c (?c ++ []) => rewrite app_nil_r; apply Permutation_refl
| |- Permutation [] ?R => rewrite ?app_nil_r; apply Permutation_refl
end).
Section o. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_SMdw : forall E op a b,
U E (SMdw op a b) = bv_wrap 64 (bv_swrap 32 (zmd_raw 32 op (U E a mod 2^32) (U E b mod 2^32))).
Proof. intros. rewrite U_of_S, S_SMdw. reflexivity. Qed.
Lemma U_SAluw : forall E op a b,
U E (SAluw op a b) = bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2^32) (U E b mod 2^32))).
Proof. intros. rewrite U_of_S, S_SAluw. reflexivity. Qed.
Definition sx32v (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).
Lemma sx32v_small : forall v, 0 <= v < 2 ^ 31 -> sx32v v = v.
Proof. intros v Hv. unfold sx32v. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma sx32v_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= sx32v v < 2 ^ 64.
Proof. intros v Hv. unfold sx32v. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma U_sext32_sx32v : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = sx32v v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, zcanon, M64, sx32v.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl].
- rewrite (Z.mod_small (v + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
- replace ((v + 2147483648) mod 4294967296) with (v + 2147483648 - 4294967296) by (apply (Zmod_unique _ _ 1); lia).
symmetry. apply (Zmod_unique _ _ (-1)); unfold M64; lia.
Qed.
Lemma U_remuw_small : forall E a b x T,
U E a = x -> U E b = T -> 0 <= x < 2 ^ 31 -> 0 < T < 2 ^ 31 ->
U E (SMdw M_REMU a b) = x mod T.
Proof.
intros E a b x T Ha Hb Hx HT. rewrite U_SMdw. cbn [zmd_raw]. rewrite Ha, Hb.
rewrite (Z.mod_small T (2 ^ 32)), (Z.mod_small x (2 ^ 32)) by lia.
replace (T =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound x T ltac:(lia)).
rewrite swrap32_id by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Definition sv_hash (n32 n33 n34 nT : nat) : sv :=
SMdw M_REMU (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff n32 0) (SLit 16)) (SAlu ALU_SLL (SOff n33 0) (SLit 8))) (SOff n34 0)) (SOff nT 0).
Lemma U_hash0 : forall E n32 n33 n34 nT (c : colour) T,
ew E n32 = Z_to_bv 64 (cR c) -> ew E n33 = Z_to_bv 64 (cG c) -> ew E n34 = Z_to_bv 64 (cB c) -> colour_ok c ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (sv_hash n32 n33 n34 nT) = hash0 T c.
Proof.
intros E n32 n33 n34 nT c T H32 H33 H34 Hc HT RT.
pose proof Hc as (Rr & Rg & Rb). unfold sv_hash, hash0.
apply U_remuw_small; [| apply (U_atom E nT T HT); lia | lia | lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E n32 (cR c) H32), (U_atom E n33 (cG c) H33), (U_atom E n34 (cB c) H34) by lia.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
rewrite (zcanon_id (cR c * 65536)), (zcanon_id (cG c * 256)) by (unfold M64; lia).
assert (L1 : Z.lor (cR c * 65536) (cG c * 256) = cR c * 65536 + cG c * 256).
{ change 65536 with (2 ^ 16). apply lor_low_disjoint; lia. }
rewrite L1. rewrite (zcanon_id (cR c * 65536 + cG c * 256)) by (unfold M64; lia).
assert (L2 : Z.lor (cR c * 65536 + cG c * 256) (cB c) = cR c * 65536 + cG c * 256 + cB c).
{ replace (cR c * 65536 + cG c * 256) with ((cR c * 256 + cG c) * 2 ^ 8) by lia. rewrite lor_low_disjoint; lia. }
rewrite L2. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_u_hash0 : forall E nu n32 n33 n34 nT (c : colour) T u,
ew E n32 = Z_to_bv 64 (cR c) -> ew E n33 = Z_to_bv 64 (cG c) -> ew E n34 = Z_to_bv 64 (cB c) -> colour_ok c ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 -> ew E nu = Z_to_bv 64 u -> 0 <= u -> u + T < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nu 0) (sv_hash n32 n33 n34 nT)) = u + hash0 T c.
Proof.
intros E nu n32 n33 n34 nT c T u H32 H33 H34 Hc HT RT Hu Ru RuT.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_hash0 E n32 n33 n34 nT c T H32 H33 H34 Hc HT RT).
rewrite (U_atom E nu u Hu) by lia. pose proof (hash0_range T c ltac:(lia)). apply zcanon_id. unfold M64; lia.
Qed.
Definition alpha8 (a : Z) : Z := if 128 <=? a then 255 else 0.
Definition sv_pix3 (n32 n33 n34 : nat) : sv :=
SAlu ALU_OR (SAlu ALU_OR (SLit 4278190080) (SAlu ALU_SLL (SOff n34 0) (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL (SOff n33 0) (SLit 8)) (SOff n32 0)).
Definition sv_pix4 (n32 n33 n34 n35 : nat) : sv :=
SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SAluw ALU_SRL (SExt true 8 (SOff n35 0)) (SLit 24)) (SLit 24)) (SAlu ALU_SLL (SOff n34 0) (SLit 16)))
(SAlu ALU_OR (SAlu ALU_SLL (SOff n33 0) (SLit 8)) (SOff n32 0)).
Definition sv_hashx (p : sv) (nT : nat) : sv :=
SMdw M_REMU (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL p (SLit 56)) (SLit 40)) (SAlu ALU_AND p (SLit 65280)))
(SAlu ALU_SRL (SAlu ALU_SLL p (SLit 40)) (SLit 56))) (SOff nT 0).
Lemma lor_disjoint_gen : forall a x k, 0 <= a -> 0 <= k -> 0 <= x < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a x = a + x.
Proof.
intros a x k Ha Hk Hx Hm. rewrite (Z_div_mod_eq_full a (2 ^ k)), Hm, Z.add_0_r.
rewrite (Z.mul_comm (2 ^ k)). apply lor_low_disjoint; first [lia | apply Z.div_pos; lia].
Qed.


Lemma U_alpha_sext8 : forall E n a, ew E n = Z_to_bv 64 a -> 0 <= a < 256 ->
U E (SAlu ALU_SLL (SAluw ALU_SRL (SExt true 8 (SOff n 0)) (SLit 24)) (SLit 24)) = alpha8 a * 2 ^ 24.
Proof.
intros E n a Hn Ha. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAluw. cbn [zalu_raw]. rewrite !U_SLit, U_SExt.
rewrite (U_atom E n a Hn) by lia. change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small a 256) by lia.
change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24. change (Z.land (zcanon 24) 63) with 24.
unfold alpha8, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
destruct (Z.leb_spec 128 a).
- replace ((a + 128) mod 256) with (a + 128 - 256) by (rewrite <- (Z.mod_small (a + 128 - 256) 256) by lia; rewrite <- (Z.mod_add _ 1 256) by lia; f_equal; lia).
replace (zcanon (a + 128 - 256 - 128)) with (2 ^ 64 + (a - 256)) by (unfold zcanon, M64; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
replace ((2 ^ 64 + (a - 256)) mod 2 ^ 32) with (2 ^ 32 + (a - 256)).
2:{ replace (2 ^ 64 + (a - 256)) with ((2 ^ 32 + (a - 256)) + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
rewrite Z.shiftr_div_pow2 by lia.
replace ((2 ^ 32 + (a - 256)) / 2 ^ 24) with 255.
2:{ apply Z.div_unique with (r := 2 ^ 24 - 256 + a); lia. }
reflexivity.
- rewrite (Z.mod_small (a + 128) 256) by lia. replace (a + 128 - 128) with a by lia. rewrite (zcanon_id a) by (unfold M64; lia).
rewrite (Z.mod_small a (2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma U_pix_alpha : forall E p A (c : colour),
colour_ok c -> 0 <= A < 256 -> U E p = A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c ->
U E (SAlu ALU_SRL p (SLit 24)) = A.
Proof.
intros E p A c (Rr & Rg & Rb) RA Hp. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hp.
change (Z.land (zcanon 24) 63) with 24. rewrite Z.shiftr_div_pow2 by lia.
replace ((A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c) / 2 ^ 24) with A
by (apply Z.div_unique with (r := cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c); lia).
apply zcanon_id. unfold M64; lia.
Qed.
Lemma land_byte_mask : forall x j, 0 <= x -> 0 <= j -> Z.land x (255 * 2 ^ j) = ((x / 2 ^ j) mod 256) * 2 ^ j.
Proof.
intros x j Hx Hj. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
change 255 with (Z.ones 8). change 256 with (2 ^ 8).
destruct (Z_lt_le_dec n j) as [Hlo|Hge].
- rewrite !Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
- rewrite !Z.mul_pow2_bits by lia.
destruct (Z_lt_le_dec (n - j) 8) as [Hlo2|Hge2].
+ rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
rewrite Bool.andb_true_r. f_equal. lia.
+ rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.
Lemma U_hashx : forall E p nT A (c : colour) T,
colour_ok c -> 0 <= A < 256 -> U E p = A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (sv_hashx p nT) = hash0 T c.
Proof.
intros E p nT A c T (Rr & Rg & Rb) RA Hp HT RT. unfold sv_hashx, hash0.
apply U_remuw_small; [| apply (U_atom E nT T HT); lia | lia | lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Hp.
change (Z.land (zcanon 56) 63) with 56. change (Z.land (zcanon 40) 63) with 40. rewrite (zcanon_id 65280) by (unfold M64; lia).
set (P := A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c).
assert (E1 : Z.shiftr (zcanon (Z.shiftl P 56)) 40 = cR c * 2 ^ 16).
{ unfold zcanon, M64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (P * 2 ^ 56) with (cR c * 2 ^ 56 + (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) * 2 ^ 64) by (subst P; lia).
rewrite Z.mod_add, Z.mod_small by lia.
symmetry. apply Z.div_unique with (r := 0); lia. }
assert (E2 : Z.land P 65280 = cG c * 2 ^ 8).
{ change 65280 with (255 * 2 ^ 8). rewrite land_byte_mask by lia. f_equal.
replace (P / 2 ^ 8) with (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) by (apply Z.div_unique with (r := cR c); lia).
replace (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) with (cG c + (A * 2 ^ 8 + cB c) * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (E3 : Z.shiftr (zcanon (Z.shiftl P 40)) 56 = cB c).
{ unfold zcanon, M64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (P * 2 ^ 40) with ((cB c * 2 ^ 56 + (cG c * 2 ^ 8 + cR c) * 2 ^ 40) + (A) * 2 ^ 64) by (subst P; lia).
rewrite Z.mod_add, Z.mod_small by lia.
symmetry. apply Z.div_unique with (r := (cG c * 2 ^ 8 + cR c) * 2 ^ 40); lia. }
rewrite E1, E2, E3. rewrite (zcanon_id (cR c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8)), (zcanon_id (cB c)) by (unfold M64; lia).
assert (L1 : Z.lor (cR c * 2 ^ 16) (cG c * 2 ^ 8) = cR c * 2 ^ 16 + cG c * 2 ^ 8).
{ apply (lor_disjoint_gen _ _ 16); try lia. rewrite Z.mod_mul. reflexivity. lia. }
rewrite L1. rewrite (zcanon_id (cR c * 2 ^ 16 + cG c * 2 ^ 8)) by (unfold M64; lia).
assert (L2 : Z.lor (cR c * 2 ^ 16 + cG c * 2 ^ 8) (cB c) = cR c * 2 ^ 16 + cG c * 2 ^ 8 + cB c).
{ apply (lor_disjoint_gen _ _ 8); try lia. replace (cR c * 2 ^ 16 + cG c * 2 ^ 8) with ((cR c * 2 ^ 8 + cG c) * 2 ^ 8) by lia.
rewrite Z.mod_mul; lia. }
rewrite L2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_add_mul3' : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff m 0) (SMd M_MUL (SOff n 0) (SLit 3))) = b + 3 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite (U_atom E m b Hm) by lia. rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite (zcanon_id (i * 3)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Definition sv_next (nh nT : nat) : sv :=
SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_XOR (SOff nh 1) (SOff nT 0)) (SLit 1)) (SLit (-1))) (SOff nh 1).
Definition sv_nextz (nh nT : nat) : sv := SAlu ALU_SRL (SAlu ALU_SLL (sv_next nh nT) (SLit 32)) (SLit 32).
Lemma U_sv_next : forall E nh nT h T,
ew E nh = Z_to_bv 64 h -> ew E nT = Z_to_bv 64 T -> 0 <= h < T -> T < 2 ^ 30 ->
U E (sv_next nh nT) = probe_next T h.
Proof.
intros E nh nT h T Hh HT Rh RT. unfold sv_next.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom_off E nh h 1 Hh), (U_atom E nT T HT) by lia.
rewrite (zcanon_id 1) by (unfold M64; lia).
unfold probe_next. destruct (Z.eqb_spec (h + 1) T) as [Heq|Hne].
- rewrite Heq, Z.lxor_nilpotent. rewrite (zcanon_id 0) by (unfold M64; lia). cbn [Z.ltb].
change (zcanon 1 + zcanon (-1)) with (2 ^ 64). change (zcanon (2 ^ 64)) with 0. rewrite Z.land_0_l. reflexivity.
- assert (Hx : Z.lxor (h + 1) T <> 0) by (intros Hx; apply Z.lxor_eq in Hx; lia).
pose proof (Z.lxor_nonneg (h + 1) T) as Hnn.
assert (Hxlt : Z.lxor (h + 1) T < 2 ^ 30).
{ apply Z.log2_lt_pow2; [lia|].
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
rewrite (zcanon_id (Z.lxor (h + 1) T)) by (unfold M64; lia).
replace (Z.lxor (h + 1) T <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). change (0 + zcanon (-1)) with (Z.ones 64). change (zcanon (Z.ones 64)) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones_low; [| lia | apply Z.log2_lt_pow2; lia]. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_sv_nextz : forall E nh nT h T,
ew E nh = Z_to_bv 64 h -> ew E nT = Z_to_bv 64 T -> 0 <= h < T -> T < 2 ^ 30 ->
U E (sv_nextz nh nT) = probe_next T h.
Proof.
intros E nh nT h T Hh HT Rh RT. unfold sv_nextz.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_sv_next E nh nT h T Hh HT Rh RT).
pose proof (probe_next_range T h Rh) as Rn.
change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (probe_next T h * 2 ^ 32)) by (unfold M64; change (2^64) with (2^32 * 2^32); nia).
rewrite Z.shiftr_div_pow2, Z.div_mul by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_u_next : forall E nu nh nT u h T,
ew E nu = Z_to_bv 64 u -> ew E nh = Z_to_bv 64 h -> ew E nT = Z_to_bv 64 T -> 0 <= h < T -> T < 2 ^ 30 ->
0 <= u -> u + T < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nu 0) (sv_nextz nh nT)) = u + probe_next T h.
Proof.
intros E nu nh nT u h T Hu Hh HT Rh RT Ru RuT.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_sv_nextz E nh nT h T Hh HT Rh RT). rewrite (U_atom E nu u Hu) by lia.
pose proof (probe_next_range T h Rh) as Rn. apply zcanon_id. unfold M64; lia.
Qed.
Lemma branch_lt_sext8 : forall E n a,
ew E n = Z_to_bv 64 a -> 0 <= a < 256 ->
branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = (128 <=? a).
Proof.
intros E n a Hn Ha. cbn [branch_taken sv_denot]. rewrite Z.add_0_r, Hn, unsigned_lit_small by lia.
rewrite (zext_low_sound true 8 a). rewrite bv_lts_signed, !signed_lit.
unfold zext_low. rewrite (zcanon_id a) by (unfold M64; lia). change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small a 256) by lia.
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite (swrap64_id 0) by (unfold half64; lia).
unfold bv_swrap at 2. unfold bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
destruct (Z.leb_spec 128 a).
- replace ((a + 128) mod 256) with (a + 128 - 256) by (rewrite <- (Z.mod_small (a + 128 - 256) 256) by lia; rewrite <- (Z.mod_add _ 1 256) by lia; f_equal; lia).
replace (zcanon (a + 128 - 256 - 128)) with (2 ^ 64 + (a - 256)) by (unfold zcanon, M64; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
rewrite zcanon_id by (unfold M64; lia). unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (a + 128) 256) by lia. replace (a + 128 - 128) with a by lia. rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id a) by (unfold M64; lia).
rewrite swrap64_id by (unfold half64; lia). apply Z.ltb_ge. lia.
Qed.
Lemma probe_facts : forall T used keys c r, 0 < T -> probe T used keys c = Some r ->
exists js, 0 <= js < T /\ r = cyc T (hash0 T c) js /\
(forall i, 0 <= i <= js ->
slot_stop (HT0 T used keys) c (cyc T (hash0 T c) i) = (i =? js)).
Proof.
intros T used keys c r HT Hp. unfold probe, find_slot in Hp.
destruct (find_off (HT0 T used keys) c) as [js|] eqn:E; [|discriminate]. injection Hp as <-.
unfold find_off in E. cbn [ht_T HT0] in E. apply ffirst_Some in E. destruct E as (H1 & H2 & H3).
exists js. split; [lia|]. split; [reflexivity|]. intros i Hi.
destruct (Z.eqb_spec i js) as [->|Hne]; [exact H2 | apply H3; lia].
Qed.
Lemma slot_stop_HT0 : forall T used keys c h,
slot_stop (HT0 T used keys) c h = (getz used h =? 0) || colour_eqb (col_at keys h) c.
Proof. reflexivity. Qed.
Lemma Z_to_bv8_inj : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z_to_bv 8 a = Z_to_bv 8 b -> a = b.
Proof.
intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
unfold bv_wrap in E. change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.
Lemma key_bytes_eq_iff : forall (c : colour) keys h,
colour_ok c -> 0 <= getz keys (3 * h) < 256 -> 0 <= getz keys (3 * h + 1) < 256 -> 0 <= getz keys (3 * h + 2) < 256 ->
([Z_to_bv 8 (cR c); Z_to_bv 8 (cG c); Z_to_bv 8 (cB c)] =
[Z_to_bv 8 (getz keys (3 * h)); Z_to_bv 8 (getz keys (3 * h + 1)); Z_to_bv 8 (getz keys (3 * h + 2))]
<-> col_at keys h = c).
Proof.
intros c keys h (Rr & Rg & Rb) R0 R1 R2. unfold col_at, mkcol. destruct c as [[r g] b]. unfold cR, cG, cB in *. cbn [fst snd] in *.
split.
- intros E.
pose proof (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) E) as E0. pose proof (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) E) as E1.
pose proof (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) E) as E2. cbn [nth] in E0, E1, E2.
apply Z_to_bv8_inj in E0; [|lia|lia]. apply Z_to_bv8_inj in E1; [|lia|lia]. apply Z_to_bv8_inj in E2; [|lia|lia].
rewrite E0, E1, E2. reflexivity.
- intros E. injection E as E0 E1 E2. rewrite E0, E1, E2. reflexivity.
Qed.
Section q.
Variable segs : list Segment.
Lemma getr_of_U : forall E ss ms (rr : reg) v,
st_ok segs E ss ms -> U E (sr_get (ss_regs ss) rr) = v -> getr (ms_regs ms) rr = Z_to_bv 64 v.
Proof. intros E ss ms rr v HS HU. rewrite (st_ok_reg _ _ _ _ rr HS), denot_lit_U, HU. reflexivity. Qed.
Lemma region_kept_same : forall E (m : word -> option byte) r, region_kept segs E m m r.
Proof. intros E m r. split; intros a Ha; auto. Qed.
Lemma val_mem_byte : forall (m : word -> option byte) a v,
mbyte segs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem segs m a 1 v.
Proof.
intros m a v Hb Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma rdn3_of_mbytes : forall (m : word -> option byte) a v0 v1 v2,
mbyte segs m a = Some (Z_to_bv 8 v0) -> mbyte segs m (a + 1) = Some (Z_to_bv 8 v1) -> mbyte segs m (a + 2) = Some (Z_to_bv 8 v2) ->
rdn segs m (Z_to_bv 64 a) 3 = Some [Z_to_bv 8 v0; Z_to_bv 8 v1; Z_to_bv 8 v2].
Proof.
intros m a v0 v1 v2 H0 H1 H2. apply rdn_mbytes. split; [reflexivity|].
intros i Hi. destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth_error Z.of_nat].
- rewrite Z.add_0_r. exact H0.
- exact H1.
- exact H2.
Qed.
Lemma st_chunk_word_g : forall E ss ms i rg p off e a v,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal 8 e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
word_mem segs (ms_mem ms) (a + off) v.
Proof.
intros E ss ms i rg p off e a v HS Hi Hb Hin Hp He Hv.
apply val_mem_word_mem.
pose proof (mem_ok_region segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
exact (val_of_chunk_ok segs E (ms_mem ms) a off 8%N e v Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma mbyte_of_frame_g : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
mbyte segs m' a = mbyte segs m a.
Proof.
intros E rs m m' a HF Ha Hout. unfold mbyte. rewrite HF; [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Lemma obj_at_app_g : forall mem a l1 l2 v1 v2,
length v1 = length l1 ->
obj_at segs mem a (l1 ++ l2) (v1 ++ v2) <-> obj_at segs mem a l1 v1 /\ obj_at segs mem a l2 v2.
Proof.
intros mem a l1. induction l1 as [|f l1 IH]; intros l2 [|x v1] v2 Hlen; cbn in Hlen |- *; try lia; [tauto|].
rewrite IH by lia. tauto.
Qed.
End q.
Lemma regs_preserved_intro_g : forall regs regs' : bvmap 5 word,
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
regs_preserved regs regs'.
Proof.
intros regs regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
unfold callee_saved in Hr.
assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hcases as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; assumption.
Qed.

Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Lemma jcall_tmp : forall E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1
(K : layout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) raw,
st_ok segs E ss ms -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw ->
(fn_pre B MR STK1 Lc Ac (ms_regs ms) (ms_mem ms) mdc ->
SR segs (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2)) ->
YK0s.ret_ok raw -> spZ (ms_regs ms) mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ (ms_regs ms) - STK1 -> spZ (ms_regs ms) <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
(forall a, inFP FP1 a -> (inFP FP a /\ a < alloc_ceiling) \/
(exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2).
Proof.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1 K raw HS Hrv HJ Hra Hcallee Hraw Hal16 Hstk1 Hlo Hhi Htp HF.
rewrite (st_ok_mkst segs E ss ms HS Hrv).
eapply SR_mono.
{ apply Hcallee. eapply (fn_pre_of_journal B MR); [exact HJ | rewrite Hra; exact Hraw | exact Hal16 | exact Hstk1 | exact Hlo | exact Hhi | exact Htp]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
eapply (journal_sub_gen B MR LAWS); [exact HJ | exact HJ1 | exact Hlo | exact Hhi | exact HF].
Qed.
Lemma journal_kept_live : forall STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2,
journal B MR STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 -> heap_ok MR Lc Ac memc mdc ->
(forall lo hi, In (lo, hi) FP1 -> exists n, hi <= lo + n /\ In (lo, n) (blocks Lc Ac) /\ ~ In (lo, n) (blocks L2 A2)) ->
forall b m i, In (b, m) (blocks Lc Ac) -> In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs memc (b + i).
Proof.
intros STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 HJ HH HFP b m i H1 H2 Hi.
destruct HJ as (_ & _ & _ & Hblk & _). apply (Hblk b m i H1 H2 Hi).
intros ((lo & hi) & Hin & Hr). cbn [fst snd] in Hr.
destruct (HFP lo hi Hin) as (n & Hn & Hlon & Hgone).
assert (Hne : (lo, n) <> (b, m)) by (intros E; rewrite E in Hgone; exact (Hgone H2)).
destruct (heap_sep_in2 B MR LAWS Lc Ac memc mdc (lo, n) (b, m) HH Hlon H1 Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia.
Qed.
Lemma journal_high : forall STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2,
journal B MR STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) -> mbyte segs mem2 a = mbyte segs memc a.
Proof. intros STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 (_ & _ & Hhigh & _) a Ha Hna. apply (proj1 (Hhigh a Ha Hna)). Qed.
End J.
End o.
Ltac mb_frame_g HF :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
rewrite (mbyte_of_frame_g _ E rs m m' _ HF); [ | lia |
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]) |]);
[ .. | destruct Hr ] ]
end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
