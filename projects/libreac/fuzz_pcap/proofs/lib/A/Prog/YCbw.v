(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbw.v for libreac/fuzz_pcap's program walk, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP01 YP03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI08 YI0t YI0m YI0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable E : env.
Definition sv_12lp (n : nat) : sv :=
SAluw ALU_SUB (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 4)) (SLit 16)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SLit 4)).
Lemma U_12lp : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (sv_12lp n) = 12 * (lp + 1).
Proof.
intros n lp Hn H0 H1. unfold sv_12lp.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (U_atom E n lp Hn) by lia.
change (Z.land (zcanon 4) 63) with 4. change (Z.land (zcanon 2) 63) with 2. change (zcanon 16) with 16. change (zcanon 4) with 4.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
rewrite (zcanon_id (lp * 16)), (zcanon_id (lp * 4)) by (rewrite M64_val; lia).
rewrite (zcanon_id (lp * 16 + 16)), (zcanon_id (lp * 4 + 4)) by (rewrite M64_val; lia).
rewrite (Z.mod_small (lp * 16 + 16)), (Z.mod_small (lp * 4 + 4)) by lia.
rewrite swrap32_small by lia. rewrite wrap64_small by lia. lia.
Qed.
Lemma U_blA : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SAluw ALU_SRL (sv_12lp n) (SLit 3)) (SLit 3)) = 12 * (lp + 1) / 8 + 3.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 12 * (lp + 1) / 8 <= 12 * (lp + 1)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 3) with 3.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 3 mod 2 ^ 32) with 3.
rewrite (U_12lp n lp Hn H0 H1). change (Z.land 3 31) with 3.
rewrite (Z.mod_small (12 * (lp + 1))) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
set (q := 12 * (lp + 1) / 8) in *.
rewrite (swrap32_small q) by lia. rewrite (wrap64_small q) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_bbA : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_SRL (SAlu ALU_SLL (sv_12lp n) (SLit 32)) (SLit 27)) (SLit MAGIC_0101)) (SLit 4))
= 384 * (lp + 1) / 255 + 4.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 384 * (lp + 1) / 255 <= 384 * (lp + 1)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 4) with 4.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. change (zcanon MAGIC_0101) with MAGIC_0101.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 27) 63) with 27.
rewrite (U_12lp n lp Hn H0 H1).
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (12 * (lp + 1) * 2 ^ 32)) by (rewrite M64_val; nia).
rewrite (Z.shiftr_div_pow2 _ 27) by lia.
replace (12 * (lp + 1) * 2 ^ 32 / 2 ^ 27) with (384 * (lp + 1)).
2:{ replace (12 * (lp + 1) * 2 ^ 32) with (384 * (lp + 1) * 2 ^ 27) by (change (2 ^ 32) with (32 * 2 ^ 27); lia).
rewrite Z.div_mul by lia. reflexivity. }
rewrite (zcanon_id (384 * (lp + 1))) by (rewrite M64_val; lia).
change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite magic0101_div by lia.
rewrite (zcanon_id (384 * (lp + 1) / 255)) by (rewrite M64_val; lia).
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_12lpM : forall n lp c, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 -> 0 < c <= 384 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit c)) (SLit c)) = c * (lp + 1).
Proof.
intros n lp c Hn H0 H1 Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit. rewrite (U_atom E n lp Hn) by lia.
rewrite (zcanon_id c) by (rewrite M64_val; lia).
rewrite (zcanon_id (lp * c)) by (rewrite M64_val; nia). replace (c * (lp + 1)) with (lp * c + c) by lia.
apply zcanon_id. rewrite M64_val. nia.
Qed.
Lemma U_blB : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SAluw ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 12)) (SLit 12)) (SLit 3)) (SLit 3)) = 12 * (lp + 1) / 8 + 3.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 12 * (lp + 1) / 8 <= 12 * (lp + 1)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 3) with 3.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 3 mod 2 ^ 32) with 3.
rewrite (U_12lpM n lp 12 Hn H0 H1 ltac:(lia)). change (Z.land 3 31) with 3.
rewrite (Z.mod_small (12 * (lp + 1))) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
set (q := 12 * (lp + 1) / 8) in *.
rewrite (swrap32_small q) by lia. rewrite (wrap64_small q) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_bbB : forall n lp, ew E n = Z_to_bv 64 lp -> 0 <= lp -> lp + 1 <= 2 ^ 27 ->
U E (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 384)) (SLit 384)) (SLit 72340172838076674)) (SLit 4))
= 384 * (lp + 1) / 255 + 4.
Proof.
intros n lp Hn H0 H1.
assert (Hq : 0 <= 384 * (lp + 1) / 255 <= 384 * (lp + 1)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 4) with 4.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. change (zcanon 72340172838076674) with MAGIC_0101.
rewrite (U_12lpM n lp 384 Hn H0 H1 ltac:(lia)).
change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite magic0101_div by lia.
rewrite (zcanon_id (384 * (lp + 1) / 255)) by (rewrite M64_val; lia).
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_add0 : forall e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.
Lemma U_arem : forall q p s nP,
ew E q = Z_to_bv 64 s -> ew E p = Z_to_bv 64 nP -> 0 <= s -> s + 2 <= nP -> nP <= 100000000 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SLit (-2))) (SOff p 0)) = nP - s - 2.
Proof.
intros q p s nP Hq Hp Hs Hsn HnP.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
rewrite (U_atom E q s Hq), (U_atom E p nP Hp) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon (-2)) with (2 ^ 64 - 2). unfold zcanon. rewrite M64_val.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma U_mul_row64 : forall nm nd m idl,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> 1 <= m <= 2048 -> 0 <= idl <= 256 ->
U E (SMd M_MUL (SOff nm (-1)) (SOff nd 0)) = (m - 1) * idl.
Proof.
intros nm nd m idl Hm Hd Rm Rd.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom_off E nm m (-1) Hm), (U_atom E nd idl Hd) by lia.
replace (m + -1) with (m - 1) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_add_small : forall a b x y,
U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof.
intros a b x y Ha Hb Hx Hy Hxy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_addw_small : forall a b x y,
U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 31 -> U E (SAluw ALU_ADD a b) = x + y.
Proof.
intros a b x y Ha Hb Hx Hy Hxy. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite Ha, Hb.
rewrite (Z.mod_small x), (Z.mod_small y) by lia. rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma U_sll1_small : forall a x, U E a = x -> 0 <= x -> 2 * x < 2 ^ 64 -> U E (SAlu ALU_SLL a (SLit 1)) = 2 * x.
Proof.
intros a x Ha Hx H2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite Ha, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma alias_base_sll1 : forall nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SLL e (SLit 1))) = sv_denot E (SOff nk 0).
Proof.
intros nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small (SOff nb 0) (SAlu ALU_SLL e (SLit 1)) base (2 * v)); try lia.
- rewrite (U_atom E nk _ Hk) by lia. reflexivity.
- apply (U_atom E nb base Hb). lia.
- apply U_sll1_small; [exact He | lia | lia].
Qed.
End f.
End d.
