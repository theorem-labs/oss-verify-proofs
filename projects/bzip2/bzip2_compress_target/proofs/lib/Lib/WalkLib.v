(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Abbreviation swrap32_id := swrap32_small.

Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (u + 2^31)%Z with ((u - 2^64 + 2^31) + 2^32 * 2^32)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_range : forall z, (-2^31 <= bv_swrap 32 z < 2^31)%Z.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  pose proof (Z.mod_pos_bound (z + 2^31) (2^32) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_mod : forall z, bv_swrap 32 (z mod 2^32) = bv_swrap 32 z.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma signed_lit_small : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2 ^ 64 `div` 2)%Z with (2^63)%Z.
  rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.
Abbreviation signed_lit := signed_lit_small.

Lemma unsigned_lit_neg : forall z, (- 2^64 <= z < 0)%Z -> bv_unsigned (Z_to_bv 64 z) = (z + 2^64)%Z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace z with ((z + 2^64) + (-1) * 2^64)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sx32_small : forall w : word, (bv_unsigned w < 2^31)%Z -> sx32 w = w.
Proof.
  intros w Hw. unfold sx32. pose proof (bv_unsigned_in_range 64 w).
  rewrite swrap32_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition errno_of (r : word) : option Z :=
  if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
  intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
  split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma errno_of_errno_ret : forall e, (1 <= e <= 4095)%Z -> errno_of (errno_ret e) = Some e.
Proof.
  intros e He. unfold errno_of. rewrite unsigned_errno_ret by lia.
  destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Lemma errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> errno_of (Z_to_bv 64 z) = None.
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

Lemma errno_of_big : forall r, (2^64 - 4096 < bv_unsigned r)%Z -> errno_of r = Some (2^64 - bv_unsigned r)%Z.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed.

(* [comment removed for export] *)
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).

(* [comment removed for export] *)
Definition sysret_val (r : word) : word :=
  match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
  match errno_of r with Some e => Z_to_bv 64 e | None => errv end.

(* [comment removed for export] *)
Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
  nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.
