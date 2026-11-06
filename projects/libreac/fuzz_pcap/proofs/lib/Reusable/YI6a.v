(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI6a.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP01 YP03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI08 YI0t YI0m YI0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable E : env.
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
Lemma U_sextw_small : forall a x, U E a = x -> 0 <= x < 2 ^ 31 -> U E (SAluw ALU_ADD a (SLit 0)) = x.
Proof.
intros a x Ha Hx. replace x with (x + 0) by lia. apply U_addw_small; [exact Ha | | lia | lia | lia].
rewrite U_SLit. reflexivity.
Qed.
Lemma U_sll1_small : forall a x, U E a = x -> 0 <= x -> 2 * x < 2 ^ 64 -> U E (SAlu ALU_SLL a (SLit 1)) = 2 * x.
Proof.
intros a x Ha Hx H2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite Ha, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma cond_eq_U : forall a b, U E a = U E b -> acond_ok E (mkAC BC_EQ a b).
Proof. intros a b H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U. apply Z.eqb_eq. exact H. Qed.
Lemma cond_ne_U : forall a b, U E a <> U E b -> acond_ok E (mkAC BC_NE a b).
Proof. intros a b H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U. apply Bool.negb_true_iff. apply Z.eqb_neq. exact H. Qed.
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
Lemma alias_sll1_base : forall nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL e (SLit 1)) (SOff nb 0)) = sv_denot E (SOff nk 0).
Proof.
intros nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small (SAlu ALU_SLL e (SLit 1)) (SOff nb 0) (2 * v) base); try lia.
- rewrite (U_atom E nk _ Hk) by lia. lia.
- apply U_sll1_small; [exact He | lia | lia].
- apply (U_atom E nb base Hb). lia.
Qed.
Lemma U_ptrchk : forall np nb e p base v,
ew E np = Z_to_bv 64 p -> ew E nb = Z_to_bv 64 base -> U E e = v ->
0 <= v < 2 ^ 31 -> 0 <= base <= p -> p < 2 ^ 64 ->
U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff np 0) (SOff nb 0)) (SAlu ALU_SLT e (SLit 0))) (SLit 1)) = 1.
Proof.
intros np nb e p base v Hp Hb He Rv Rb Rp.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E np p Hp), (U_atom E nb base Hb) by lia.
replace (p <? base) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite He, !U_SLit. change (zcanon 0) with 0. change (zcanon 1) with 1.
rewrite (swrap64_id v) by (unfold half64; lia). rewrite (swrap64_id 0) by (unfold half64; lia).
replace (v <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End d.
End c.
