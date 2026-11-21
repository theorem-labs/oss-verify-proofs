(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac ITree Nodes SysStep Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Definition munmap_ret (a : range_ans) : word :=
  match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
  match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
  intros Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.


Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
  if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
  else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].


Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

Definition brk_res (cur req : Z) (a : brk_ans) : Z := match a with BrkGrown => req | BrkSame => cur end.
Definition brk_mem (m : word -> option byte) (cur req : Z) (a : brk_ans) : word -> option byte :=
  match a with
  | BrkGrown => match brk_new_pages cur req with Some (lo, n) => apply_zeros m [(wa lo, Z_to_bv 64 n)] | None => m end
  | BrkSame => m
  end.

Lemma land_neg_aligned cur : (0 < cur < 2^64)%Z -> (cur mod 4096 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 (0 + - cur))) 4095 = 0%Z.
Proof.
  intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  replace ((0 + - cur) mod 2^64)%Z with ((2^52 - cur / 4096) * 4096)%Z by (Z.div_mod_to_equations; lia).
  change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12)%Z with 4096%Z. apply Z.mod_mul. lia.
Qed.
