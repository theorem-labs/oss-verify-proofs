(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Definition bsPutUInt32_specS (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (u lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = sx32 (Z_to_bv 64 u) -> 0 <= u < 4294967296 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 16 <= ARR2_SIZE ->
  evt segs (bsPutUInt32_post segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bsPutUInt32_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsPutUInt32 I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Lemma sx32_low32 : forall u, 0 <= u < 4294967296 -> bv_unsigned (sx32 (Z_to_bv 64 u)) mod 4294967296 = u.
Proof. intros u Hu. pose proof (low32_sx32 (Z_to_bv 64 u)) as L. rewrite low32_lit in L. rewrite L. apply Z.mod_small. exact Hu. Qed.
Lemma sx32_shl_mod64 : forall u k, 0 <= u < 4294967296 -> 32 <= k ->
  (bv_unsigned (sx32 (Z_to_bv 64 u)) * 2 ^ k) mod 18446744073709551616 = (u * 2 ^ k) mod 18446744073709551616.
Proof.
  intros u k Hu Hk. pose proof (sx32_low32 u Hu) as L.
  set (x := bv_unsigned (sx32 (Z_to_bv 64 u))) in *.
  assert (E : x = u + 4294967296 * (x / 4294967296)) by (pose proof (Z.div_mod x 4294967296 ltac:(lia)); lia).
  rewrite E, Z.mul_add_distr_r.
  replace (4294967296 * (x / 4294967296) * 2 ^ k) with ((x / 4294967296) * 2 ^ (k - 32) * 18446744073709551616).
  2:{ change 18446744073709551616 with (2 ^ 64). change 4294967296 with (2 ^ 32).
      rewrite <- !Z.mul_assoc, <- Z.pow_add_r by lia. replace (k - 32 + 64) with (32 + (k - 32 + 32)) by lia.
      rewrite Z.pow_add_r by lia. replace (k - 32 + 32) with k by lia. lia. }
  rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Lemma sx32_mod256 : forall u, 0 <= u < 4294967296 -> bv_unsigned (sx32 (Z_to_bv 64 u)) mod 256 = u mod 256.
Proof.
  intros u Hu. pose proof (sx32_low32 u Hu) as L.
  rewrite <- (Z.mod_mod_divide _ 4294967296 256) by (exists 16777216; reflexivity). rewrite L. reflexivity.
Qed.

Lemma sx32_land255 : forall u, 0 <= u < 4294967296 -> Z.land (bv_unsigned (sx32 (Z_to_bv 64 u))) 255 = Z.land u 255.
Proof. intros u Hu. rewrite !land255_mod. apply sx32_mod256. exact Hu. Qed.
Lemma sx32_shl40 : forall u, 0 <= u < 4294967296 ->
  (bv_unsigned (sx32 (Z_to_bv 64 u)) * 1099511627776) mod 18446744073709551616 = (u * 1099511627776) mod 18446744073709551616.
Proof. intros u Hu. change 1099511627776 with (2 ^ 40). apply sx32_shl_mod64; lia. Qed.
Lemma sx32_shl48 : forall u, 0 <= u < 4294967296 ->
  (bv_unsigned (sx32 (Z_to_bv 64 u)) * 281474976710656) mod 18446744073709551616 = (u * 281474976710656) mod 18446744073709551616.
Proof. intros u Hu. change 281474976710656 with (2 ^ 48). apply sx32_shl_mod64; lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_low32_div24 : forall u, 0 <= u < 4294967296 -> bv_unsigned (sx32 (Z_to_bv 64 u)) mod 4294967296 / 16777216 = u / 16777216.
Proof. intros u Hu. rewrite sx32_low32 by exact Hu. reflexivity. Qed.

End ACeilS1.
