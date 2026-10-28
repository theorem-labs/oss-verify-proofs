(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BSeqExec BAgentLib BSymExec2 BSymExec2Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BBytes.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma bt_ne_add_lits : forall (x : word) c1 c2,
  (c1 - c2) mod 2 ^ 64 <> 0 ->
  branch_taken BC_NE (alu64 ALU_ADD x (Z_to_bv 64 c1)) (alu64 ALU_ADD x (Z_to_bv 64 c2)) = true.
Proof.
  intros x c1 c2 H. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Bool.negb_true_iff. apply Z.eqb_neq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (u64_range x) as Hx. intros E. apply H.
  rewrite Zplus_mod_idemp_r in E. rewrite Zplus_mod_idemp_r in E.
  replace (c1 - c2) with ((bv_unsigned x + c1) - (bv_unsigned x + c2)) by lia.
  rewrite Zminus_mod, E, <- Zminus_mod, Z.sub_diag. reflexivity.
Qed.

Lemma lxor_ones64 : forall w, 0 <= w < 2 ^ 64 -> Z.lxor w (2 ^ 64 - 1) = 2 ^ 64 - 1 - w.
Proof.
  intros w Hw. change (2 ^ 64 - 1) with 18446744073709551615 at 1. rewrite lnot_mod64 by lia.
  unfold Z.lnot. rewrite <- Z.sub_1_r. Z.div_mod_to_equations. lia.
Qed.

Lemma bt_ltu_not_false : forall (x : word) c n,
  0 <= bv_unsigned x + c -> bv_unsigned x + c + n <= 2 ^ 64 - 1 -> 0 <= n ->
  branch_taken BC_LTU (alu64 ALU_XOR (alu64 ALU_ADD x (Z_to_bv 64 c)) (Z_to_bv 64 (-1))) (Z_to_bv 64 n) = false.
Proof.
  intros x c n H1 H2 Hn. cbn [branch_taken alu64 alu]. unfold bv_ltu. apply Z.ltb_ge.
  rewrite bv_xor_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (u64_range x) as Hx.
  replace ((bv_unsigned x + c mod 2 ^ 64) mod 2 ^ 64) with (bv_unsigned x + c) by (rewrite Zplus_mod_idemp_r, Z.mod_small; lia).
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_ones64 by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bt_eq_and_or_lit_false : forall (x : word) k c,
  0 <= k < 2 ^ 64 -> Z.land k 15 <> 0 ->
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 k) (alu64 ALU_ADD x (Z_to_bv 64 c))) (Z_to_bv 64 15)) (Z_to_bv 64 0) = false.
Proof.
  intros x k c Hk Hk15. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_neq.
  rewrite bv_and_unsigned, bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (15 mod 2 ^ 64) with 15. change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small k) by lia.
  set (u := bv_unsigned (x + Z_to_bv 64 c)%bv). clearbody u.
  rewrite Z.land_lor_distr_l. intros E.
  apply Z.lor_eq_0_iff in E. destruct E as [E _]. exact (Hk15 E).
Qed.

Lemma land_add_mask : forall u c m, u mod 16 = 0 -> (m = 3 \/ m = 7 \/ m = 15) ->
  Z.land ((u + c) mod 2 ^ 64) m = c mod (m + 1).
Proof.
  intros u c m Hu Hm.
  assert (E : exists k, 2 <= k <= 4 /\ m = Z.ones k /\ m + 1 = 2 ^ k).
  { destruct Hm as [->|[->| ->]]; [exists 2 | exists 3 | exists 4]; (split; [lia|split; reflexivity]). }
  destruct E as (k & Hk & -> & Ek). rewrite Z.land_ones by lia. rewrite Ek.
  assert (D : exists q, 16 = 2 ^ k * q /\ 0 < q).
  { exists (2 ^ (4 - k)). split; [|apply Z.pow_pos_nonneg; lia].
    rewrite <- Z.pow_add_r by lia. replace (k + (4 - k)) with 4 by lia. reflexivity. }
  destruct D as (q & Hq & Hq0).
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (D64 : exists r, 2 ^ 64 = 2 ^ k * r).
  { exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. reflexivity. }
  destruct D64 as (r & Hr).
  set (v := (u + c) mod 2 ^ 64).
  assert (Hv : exists a, v = u + c - 2 ^ 64 * a) by (exists ((u + c) / 2 ^ 64); subst v; Z.div_mod_to_equations; lia).
  destruct Hv as (a & ->).
  assert (Hu' : exists b, u = 16 * b) by (exists (u / 16); Z.div_mod_to_equations; lia).
  destruct Hu' as (b & ->).
  replace (16 * b + c - 2 ^ 64 * a) with (c + (b * q - r * a) * 2 ^ k) by (rewrite Hr; nia).
  apply Z_mod_plus_full.
Qed.

Lemma bt_eq_and_add_lit_false : forall (x : word) c m,
  bv_unsigned x mod 16 = 0 -> (m = 3 \/ m = 7 \/ m = 15) -> c mod (m + 1) <> 0 ->
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_ADD x (Z_to_bv 64 c)) (Z_to_bv 64 m)) (Z_to_bv 64 0) = false.
Proof.
  intros x c m Hx Hm Hc. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_neq.
  rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small m) by lia. rewrite Zplus_mod_idemp_r.
  rewrite land_add_mask by assumption. exact Hc.
Qed.

Lemma bt_ne_and_add_lit_true : forall (x : word) c m,
  bv_unsigned x mod 16 = 0 -> (m = 3 \/ m = 7 \/ m = 15) -> c mod (m + 1) <> 0 ->
  branch_taken BC_NE (alu64 ALU_AND (alu64 ALU_ADD x (Z_to_bv 64 c)) (Z_to_bv 64 m)) (Z_to_bv 64 0) = true.
Proof.
  intros x c m Hx Hm Hc. pose proof (bt_eq_and_add_lit_false x c m Hx Hm Hc) as E. cbn [branch_taken] in E |- *.
  rewrite E. reflexivity.
Qed.

Lemma bt_eq_and_add_lit_true : forall (x : word) c m,
  bv_unsigned x mod 16 = 0 -> (m = 3 \/ m = 7 \/ m = 15) -> c mod (m + 1) = 0 ->
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_ADD x (Z_to_bv 64 c)) (Z_to_bv 64 m)) (Z_to_bv 64 0) = true.
Proof.
  intros x c m Hx Hm Hc. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_eq.
  rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small m) by lia. rewrite Zplus_mod_idemp_r.
  rewrite land_add_mask by assumption. exact Hc.
Qed.

Lemma bt_ne_and_add_lit_false : forall (x : word) c m,
  bv_unsigned x mod 16 = 0 -> (m = 3 \/ m = 7 \/ m = 15) -> c mod (m + 1) = 0 ->
  branch_taken BC_NE (alu64 ALU_AND (alu64 ALU_ADD x (Z_to_bv 64 c)) (Z_to_bv 64 m)) (Z_to_bv 64 0) = false.
Proof.
  intros x c m Hx Hm Hc. pose proof (bt_eq_and_add_lit_true x c m Hx Hm Hc) as E. cbn [branch_taken] in E |- *.
  rewrite E. reflexivity.
Qed.

Lemma u_add_lit : forall (x : word) c, 0 <= bv_unsigned x + c < 2 ^ 64 ->
  bv_unsigned (alu64 ALU_ADD x (Z_to_bv 64 c)) = bv_unsigned x + c.
Proof.
  intros x c H. cbn [alu64 alu]. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma bt_ltu_add_lits : forall (x : word) c1 c2 (b : bool),
  0 <= bv_unsigned x + c1 < 2 ^ 64 -> 0 <= bv_unsigned x + c2 < 2 ^ 64 ->
  (if b then c1 < c2 else c2 <= c1) ->
  branch_taken BC_LTU (alu64 ALU_ADD x (Z_to_bv 64 c1)) (alu64 ALU_ADD x (Z_to_bv 64 c2)) = b.
Proof.
  intros x c1 c2 b H1 H2 Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u_add_lit by assumption.
  destruct b; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma bt_geu_add_lits : forall (x : word) c1 c2 (b : bool),
  0 <= bv_unsigned x + c1 < 2 ^ 64 -> 0 <= bv_unsigned x + c2 < 2 ^ 64 ->
  (if b then c2 <= c1 else c1 < c2) ->
  branch_taken BC_GEU (alu64 ALU_ADD x (Z_to_bv 64 c1)) (alu64 ALU_ADD x (Z_to_bv 64 c2)) = b.
Proof.
  intros x c1 c2 b H1 H2 Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u_add_lit by assumption.
  destruct b; cbn [negb]; [rewrite (proj2 (Z.ltb_ge _ _)) by lia | rewrite (proj2 (Z.ltb_lt _ _)) by lia]; reflexivity.
Qed.

Lemma bt_eq_add_lits_false : forall (x : word) c1 c2,
  (c1 - c2) mod 2 ^ 64 <> 0 ->
  branch_taken BC_EQ (alu64 ALU_ADD x (Z_to_bv 64 c1)) (alu64 ALU_ADD x (Z_to_bv 64 c2)) = false.
Proof.
  intros x c1 c2 H. pose proof (bt_ne_add_lits x c1 c2 H) as E. cbn [branch_taken] in E |- *.
  destruct (bv_eqb _ _); [discriminate|reflexivity].
Qed.

Ltac asc_br :=
  first
    [ apply bt_ne_add_lits; vm_compute; discriminate
    | apply bt_eq_add_lits_false; vm_compute; discriminate
    | apply bt_ltu_not_false; lia
    | apply bt_eq_and_or_lit_false; [lia | vm_compute; discriminate]
    | apply bt_eq_and_add_lit_false; [assumption | lia | vm_compute; discriminate]
    | apply bt_ne_and_add_lit_true; [assumption | lia | vm_compute; discriminate]
    | apply bt_eq_and_add_lit_true; [assumption | lia | reflexivity]
    | apply bt_ne_and_add_lit_false; [assumption | lia | reflexivity]
    | apply bt_ltu_add_lits; cbv iota; lia
    | apply bt_geu_add_lits; cbv iota; lia ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
