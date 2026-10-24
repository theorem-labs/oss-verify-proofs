(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Adapted from the pinned cgif YN3e stack-alignment and envp alias proofs.
    These are proved equalities in the original initial-state interpretation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK1b YP0m YP0e YP09 YP02 YP0l YP06 YP03 YP08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Ltac zmod_elim x M :=
  let q := fresh "q" in let r := fresh "r" in
  let Hq := fresh "Hdm" in let Hr := fresh "Hmb" in
  pose proof (Z.div_mod x M ltac:(lia)) as Hq;
  pose proof (Z.mod_pos_bound x M ltac:(lia)) as Hr;
  remember (x / M) as q eqn:Heqq; clear Heqq;
  remember (x mod M) as r eqn:Heqr; clear Heqr.

Lemma negw_and3_zero : forall u : Z, u mod 16 = 0 ->
  zalu64 ALU_AND (zalu32 ALU_SUB 0 (u + -368)) 3 = 0.
Proof.
  intros u Hu.
  unfold zalu64, zalu32, zcanon, zu32, M64, M32. cbn [zalu_raw].
  rewrite (Z.mod_small 3), (Z.mod_small 0) by lia.
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32).
  zmod_elim u 16.
  zmod_elim (u + -368) (2^32).
  zmod_elim (0 - r0 + 2 ^ 31) (2^32).
  zmod_elim (r1 - 2 ^ 31) (2^64).
  zmod_elim r2 (2^64).
  zmod_elim r3 (2^2).
  rewrite Z.mod_small by lia. lia.
Qed.

Definition z_alias_memset : sv * sv :=
  (SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 0 (-368))) (SLit 3), SLit 0).
Definition z_alias_envp : sv * sv :=
  (SAlu ALU_ADD (SOff 0 16) (SAlu ALU_SLL (SOff 3 0) (SLit 3)), SOff 4 0).

Lemma z_alias_memset_ok : forall sp argv envp xw xd,
  valid_sp sp ->
  sv_denot (E0 sp argv envp xw xd) (fst z_alias_memset) =
  sv_denot (E0 sp argv envp xw xd) (snd z_alias_memset).
Proof.
  intros sp argv envp xw xd Hsp.
  cbn [fst snd z_alias_memset sv_denot].
  rewrite zalu32_sound, zalu64_sound. f_equal. apply negw_and3_zero.
  rewrite (ew0 sp argv envp). exact (proj2 (proj2 Hsp)).
Qed.

Lemma z_alias_envp_ok : forall sp argv envp xw xd,
  valid_sp sp -> valid_argv argv -> valid_envp envp ->
  sv_denot (E0 sp argv envp xw xd) (fst z_alias_envp) =
  sv_denot (E0 sp argv envp xw xd) (snd z_alias_envp).
Proof.
  intros sp argv envp xw xd Hsp Hva Hve.
  cbn [fst snd z_alias_envp sv_denot].
  rewrite !zalu64_sound.
  rewrite (ew0 sp argv envp), (ew3 sp argv envp Hva), (ew4 sp argv envp Hsp Hva Hve).
  pose proof (layout_facts sp argv envp Hsp Hva Hve) as L.
  pose proof (proj1 Hva) as HA. unfold SP_LO, SP_HI in L.
  apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
  change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  rewrite !Z.add_0_r. rewrite !(Z.mod_small _ (2^64)) by lia. lia.
Qed.

Set Printing Fully Qualified.
Print Assumptions z_alias_memset_ok.
Print Assumptions z_alias_envp_ok.
