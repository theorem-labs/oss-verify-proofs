(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
Import ListNotations.
Open Scope bv_scope.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38557618280.2000004S2Hz".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38557618280.2000004S2Hz".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Ltac mlia := Z.div_mod_to_equations; lia.
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv)%Z W -> (A <= a)%Z -> (a + n <= A + N)%Z -> (0 <= n)%Z -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. Local Ltac2 Set LiaHints.tbl := fun () => "0010>15083882462.1200000;S3Hiv2Ha2Hn".
split; [lia | exact IH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0060=33107249241.037009530087.538649584363.753892488832.763374555410.768399279967.400000100800900:00;00?SS2Hb2HsSSSS2IH".
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=15384169642.517508899659.829011858828.863368328716.500000400700:00;S2HbS1lS1nS".
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
