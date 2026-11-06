(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ02 YQ04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI01 YI07 YI03 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable E : env.
Lemma U_slli32_srli31 : forall a x, U E a = x -> 0 <= x < 2 ^ 31 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 31)) = 2 * x.
Proof.
intros a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 31) 63) with 31.
rewrite Ha, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (rewrite M64_val; split; [|change (2 ^ 64) with (2 ^ 32 * 2 ^ 32)]; nia).
change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma U_map_idx : forall nm nd nc m idl c,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> ew E nc = Z_to_bv 64 c ->
1 <= m <= 2048 -> 0 <= idl <= 256 -> 0 <= c < 256 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff nm (-1)) (SOff nd 0)) (SOff nc 0)) = (m - 1) * idl + c.
Proof.
intros nm nd nc m idl c Hm Hd Hc Rm Rd Rc.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply (U_add_small E _ _ ((m - 1) * idl) c (U_mul_row64 E nm nd m idl Hm Hd Rm Rd) (U_atom E nc c Hc ltac:(lia))); lia.
Qed.
Lemma U_mulw_row : forall nm nd m idl,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> 1 <= m <= 2048 -> 0 <= idl <= 256 ->
U E (SMdw M_MUL (SOff nm (-1)) (SOff nd 0)) = (m - 1) * idl.
Proof.
intros nm nd m idl Hm Hd Rm Rd.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite (U_atom_off E nm m (-1) Hm), (U_atom E nd idl Hd) by lia.
replace (m + -1) with (m - 1) by lia. rewrite (Z.mod_small (m - 1)), (Z.mod_small idl) by lia.
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma U_sw_idx : forall nm nd nc m idl c,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> ew E nc = Z_to_bv 64 c ->
1 <= m <= 2048 -> 0 <= idl <= 256 -> 0 <= c < 256 ->
U E (SAlu ALU_ADD (SMdw M_MUL (SOff nm (-1)) (SOff nd 0)) (SOff nc 0)) = (m - 1) * idl + c.
Proof.
intros nm nd nc m idl c Hm Hd Hc Rm Rd Rc.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply (U_add_small E _ _ ((m - 1) * idl) c (U_mulw_row nm nd m idl Hm Hd Rm Rd) (U_atom E nc c Hc ltac:(lia))); lia.
Qed.
Lemma alias_base_zext2 : forall nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v < 2 ^ 31 -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL e (SLit 32)) (SLit 31))) = sv_denot E (SOff nk 0).
Proof.
intros nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small E (SOff nb 0) _ base (2 * v)); try lia.
- rewrite (U_atom E nk _ Hk) by lia. reflexivity.
- apply (U_atom E nb base Hb). lia.
- apply U_slli32_srli31; [exact He | lia].
Qed.
End f.
Lemma aconds_ok_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|c l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
Lemma aalias_ok_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
End d.
