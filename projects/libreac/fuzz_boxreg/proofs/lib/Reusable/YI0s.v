(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0s.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YP0m YP0e YP09 YP01 YP03.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI08 YI0t YI0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable E : env.
Lemma M64_val : M64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma U_add0 : forall a, U E (SAlu ALU_ADD a (SLit 0)) = U E a.
Proof.
intros a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
pose proof (U_range E a). rewrite Z.add_0_r. apply zcanon_id. exact H.
Qed.
Lemma U_idl2 : forall n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SAlu ALU_SLL (SOff n 0) (SLit 1)) = 2 * idl.
Proof.
intros n idl Hn Hidl.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1. rewrite (U_atom E n idl Hn) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_tisz : forall n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SMd M_MUL (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = 2 * idl * idl.
Proof.
intros n idl Hn Hidl.
assert (Hsq : 2 * idl * idl <= 2 * 256 * 256) by nia.
assert (Hsq0 : 0 <= 2 * idl * idl) by nia.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 1) 63) with 1. rewrite (U_atom E n idl Hn) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (idl * 2)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_tmsz : forall n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SMd M_MUL (SOff n 0) (SLit 4098)) = 4098 * idl.
Proof.
intros n idl Hn Hidl.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. rewrite (U_atom E n idl Hn) by lia.
change (zcanon 4098) with 4098. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_epc : forall n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SAlu ALU_SUB (SLit 0) (SOff n (-4094))) = 4094 - idl.
Proof.
intros n idl Hn Hidl.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
change (zcanon 0) with 0. unfold zcanon. rewrite M64_val.
rewrite <- (Z.mod_add (idl + -4094) 1 (2 ^ 64)) by lia.
rewrite (Z.mod_small (idl + -4094 + 1 * 2 ^ 64)) by lia.
rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia.
replace (0 - (idl + -4094 + 1 * 2 ^ 64) + 1 * 2 ^ 64) with (4094 - idl) by lia. apply Z.mod_small. lia.
Qed.
Lemma U_maxres : forall n p idl nP,
ew E n = Z_to_bv 64 idl -> ew E p = Z_to_bv 64 nP -> 2 <= idl <= 256 -> 1 <= nP <= 100000000 ->
U E (SMdw M_DIVU (SOff p 0) (SAlu ALU_SUB (SLit 0) (SOff n (-4094)))) = nP / (4094 - idl).
Proof.
intros n p idl nP Hn Hp Hidl HnP.
assert (Hq : 0 <= nP / (4094 - idl) <= nP).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite (U_epc n idl Hn Hidl), (U_atom E p nP Hp) by lia.
rewrite (Z.mod_small nP), (Z.mod_small (4094 - idl)) by lia.
replace (4094 - idl =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma U_ldsz : forall n p idl nP,
ew E n = Z_to_bv 64 idl -> ew E p = Z_to_bv 64 nP -> 2 <= idl <= 256 -> 1 <= nP <= 100000000 ->
U E (SAlu ALU_SLL
(SAlu ALU_ADD
(SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_DIVU (SOff p 0) (SAlu ALU_SUB (SLit 0) (SOff n (-4094)))) (SLit 32)) (SLit 32))
(SOff p 2))
(SLit 1)) = 2 * (nP / (4094 - idl) + nP + 2).
Proof.
intros n p idl nP Hn Hp Hidl HnP.
assert (Hq : 0 <= nP / (4094 - idl) <= nP).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SLit. change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_maxres n p idl nP Hn Hp Hidl HnP). rewrite (U_atom_off E p nP 2 Hp) by lia.
set (q := nP / (4094 - idl)) in *.
rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (q * 2 ^ 32)) by (rewrite M64_val; split; [|change (2 ^ 64) with (2 ^ 32 * 2 ^ 32)]; nia).
rewrite Z.div_mul by lia. rewrite (zcanon_id q) by (rewrite M64_val; lia).
rewrite (zcanon_id (q + (nP + 2))) by (rewrite M64_val; lia).
change (2 ^ 1) with 2. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_nPm1 : forall p nP,
ew E p = Z_to_bv 64 nP -> 1 <= nP <= 100000000 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff p 0) (SLit 32)) (SLit (-4294967296))) (SLit 32)) = nP - 1.
Proof.
intros p nP Hp HnP.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite (U_atom E p nP Hp) by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (nP * 2 ^ 32)) by (rewrite M64_val; split; [|change (2 ^ 64) with (2 ^ 32 * 2 ^ 32)]; nia).
change (zcanon (-4294967296)) with (2 ^ 64 - 2 ^ 32).
replace (nP * 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with ((nP - 1) * 2 ^ 32 + 1 * 2 ^ 64) by lia.
unfold zcanon at 2. rewrite M64_val, Z.mod_add by lia.
rewrite (Z.mod_small ((nP - 1) * 2 ^ 32)) by (split; [|change (2 ^ 64) with (2 ^ 32 * 2 ^ 32)]; nia).
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_12L : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 12)) (SLit 12)) = 12 * (lp + 1).
Proof.
intros n lp Hn H0 H1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
change (zcanon 12) with 12. rewrite (U_atom E n lp Hn) by lia.
rewrite (zcanon_id (lp * 12)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_384L : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 384)) (SLit 384)) = 384 * (lp + 1).
Proof.
intros n lp Hn H0 H1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
change (zcanon 384) with 384. rewrite (U_atom E n lp Hn) by lia.
rewrite (zcanon_id (lp * 384)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_bl : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SAluw ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 12)) (SLit 12)) (SLit 3)) (SLit 3)) = 12 * (lp + 1) / 8 + 3.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 12 * (lp + 1) / 8 <= 12 * (lp + 1)).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 3) with 3.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 3 mod 2 ^ 32) 31) with 3.
rewrite (U_12L n lp Hn H0 H1). rewrite (Z.mod_small (12 * (lp + 1))) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite swrap32_small by lia. rewrite (wrap64_small (12 * (lp + 1) / 8)) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_bb : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 384)) (SLit 384)) (SLit MAGIC_0101)) (SLit 4))
= 384 * (lp + 1) / 255 + 4.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 384 * (lp + 1) / 255 <= 384 * (lp + 1)).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 4) with 4.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. change (zcanon MAGIC_0101) with MAGIC_0101.
rewrite (U_384L n lp Hn H0 H1).
change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite magic0101_div by lia.
rewrite (zcanon_id (384 * (lp + 1) / 255)) by (rewrite M64_val; lia).
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_tcnt : forall p q nP s,
ew E p = Z_to_bv 64 nP -> ew E q = Z_to_bv 64 s -> 1 <= nP <= 100000000 -> 0 <= s -> s + 1 < nP - 1 ->
U E (SAlu ALU_SUB (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff p 0) (SLit 32)) (SLit (-4294967296))) (SLit 32)) (SOff q 1))
= nP - 1 - (s + 1).
Proof.
intros p q nP s Hp Hq HnP Hs Hs1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_nPm1 p nP Hp HnP). rewrite (U_atom_off E q s 1 Hq) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_tgrd : forall q k s nimg,
ew E q = Z_to_bv 64 s -> ew E k = Z_to_bv 64 nimg -> 0 <= s -> 2 ^ 63 <= nimg < 2 ^ 64 -> s + 1 < 2 ^ 62 ->
U E (SAlu ALU_AND
(SAlu ALU_ADD (SAlu ALU_SLTU (SOff k 0) (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SLit (-1))) (SOff k 0))) (SLit (-1)))
(SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SLit (-1))) (SOff k 0)))
= nimg - (s + 1).
Proof.
intros q k s nimg Hq Hk Hs Hn Hs1.
assert (HT : U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SLit (-1))) (SOff k 0)) = nimg - (s + 1)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
rewrite (U_atom E q s Hq), (U_atom E k nimg Hk) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon. rewrite M64_val.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite HT, (U_atom E k nimg Hk), U_SLit by lia.
replace (nimg <? nimg - (s + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
change (zcanon (-1)) with (2 ^ 64 - 1).
change (zcanon (zcanon 0 + (2 ^ 64 - 1))) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_mul_atoms : forall a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
U E (SMd M_MUL (SOff a 0) (SOff b 0)) = x * y.
Proof.
intros a b x y Ha Hb Hx Hy. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. rewrite M64_val.
split; [nia|]. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). apply Z.mul_lt_mono_nonneg; lia.
Qed.
Lemma maxres_bounds : forall idl nP, 2 <= idl <= 256 -> 0 <= nP ->
(nP / (4094 - idl)) * (4094 - idl) <= nP < (nP / (4094 - idl) + 1) * (4094 - idl) /\ 0 <= nP / (4094 - idl).
Proof.
intros idl nP Hidl HnP.
pose proof (Z.div_mod nP (4094 - idl) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound nP (4094 - idl) ltac:(lia)) as Hmb.
split; [| apply Z.div_pos; lia]. nia.
Qed.
End d.
End c.
