(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for fuzz_manifest image B (asan-ubsan), piece B5 of
   the fuzz_manifest image-B piece list (row B5). U_not is copied from proofs/cgif/cgif_file_fuzzer/lib/YE2y.v:427
   and U_add2 from proofs/cgif/cgif_file_fuzzer/lib/YN37.v:83 (origin/ossv/recipes), statements unchanged; U_not's
   proof uses this unit's lib/Reusable/YI08.v lxor_allones in place of YE2y's lxor_ones. The released not+bltu guard
   lemmas are YE2y.v:446 br_ovf_false and YE2b.v:48 br_novf_geu (register atoms, bounded values);
   fmt_not_ltu_not states the same guard for any operands under U p + U n < 2^64. The branch conditions at the U
   level and U_lit are this unit's lib/Reusable/YI04.v:213-233 (branch_eq_U, branch_ne_U, branch_ltu_U,
   branch_geu_U, U_lit), used, not restated. New here: the signed branch conditions, the remaining operand shapes
   and the class lemmas K1, K3-K7 for the guard shapes fm.asan-ubsan's walked code uses. *)
(* UBSan trap guards of fm.asan-ubsan (trap mode: each check branches to an `unimp`, an ERROR under both
   statements). A walk that stops at a guard branch (psrr_branch_tok / SR_sym_branch) gets, on the trap arm,
     H : branch_taken c (sv_denot E a) (sv_denot E b) = true.
   The lemmas below turn H into its arithmetic content over U / Sg, for the operand shapes the symbolic executor
   builds at these guards (s_alu keeps `not x` as SAlu ALU_XOR x (SLit (-1)), `seqz`/`snez` as ALU_SLTU unless the
   facts decide them, `addiw` as SAluw). `fm_trap_arith H` rewrites H into a Z (in)equality; `fm_kill_trap H` then
   closes the goal by lia from the walk's facts. The guard list, each guard's shape and the fact that refutes it:
   the B5 guard table FM-B-TRAPS.md kept by the piece's lane (fm.asan-ubsan pin ca61e5c9eabc...). *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YP0m YP0e YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI08.
Open Scope Z_scope.

(* ---- signed branch conditions at the Sg level (the unsigned ones are YI04's branch_*_U) ---- *)
Lemma fmt_br_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.
Lemma fmt_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.

(* ---- the operand shapes ---- *)
(* copied from cgif_file_fuzzer lib/YE2y.v:427 *)
Lemma U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
  intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). pose proof (U_range E v) as Hr. unfold M64 in Hr.
  rewrite YI08.lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* copied from cgif_file_fuzzer lib/YN37.v:83 *)
Lemma U_add2 : forall E a b, U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = U E a + U E b.
Proof.
  intros E a b H. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
  rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fmt_U_add_wrap : forall E a b, 2 ^ 64 <= U E a + U E b -> U E (SAlu ALU_ADD a b) = U E a + U E b - 2 ^ 64.
Proof.
  intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64.
  pose proof (U_range E a). pose proof (U_range E b). unfold M64 in *.
  symmetry. apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma fmt_U_sub : forall E a b, U E b <= U E a -> U E (SAlu ALU_SUB a b) = U E a - U E b.
Proof.
  intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id.
  pose proof (U_range E a). pose proof (U_range E b). unfold M64 in *. lia.
Qed.
Lemma fmt_U_sltu : forall E a b, U E (SAlu ALU_SLTU a b) = if U E a <? U E b then 1 else 0.
Proof.
  intros E a b. rewrite U_SAlu. cbn [zalu_raw].
  destruct (U E a <? U E b); apply zcanon_id; unfold M64; lia.
Qed.
Lemma fmt_U_xor01 : forall E a b, (U E a = 0 \/ U E a = 1) -> (U E b = 0 \/ U E b = 1) ->
  U E (SAlu ALU_XOR a b) = if U E a =? U E b then 0 else 1.
Proof.
  intros E a b Ha Hb. rewrite U_SAlu. cbn [zalu_raw].
  destruct Ha as [-> | ->]; destruct Hb as [-> | ->]; vm_compute; reflexivity.
Qed.
Lemma fmt_U_litn : forall E z, - 2 ^ 64 <= z < 0 -> U E (SLit z) = 2 ^ 64 + z.
Proof.
  intros E z H. rewrite U_SLit. unfold zcanon, M64. symmetry. apply Z.mod_unique_pos with (q := -1); lia.
Qed.

(* ---- the guard classes: each says the trap arm of that guard is not taken ---- *)
(* K1: beq x, k  (pointer + k wraps, or p - k reaches null): refuted by U x <> U k. *)
Lemma fmt_eq_not : forall E a b, U E a <> U E b -> branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b H. rewrite branch_eq_U. apply Z.eqb_neq. exact H. Qed.
(* K1n: a bne whose fall-through is `j trap`: refuted by U x <> U k (the bne is TAKEN). *)
Lemma fmt_ne_taken : forall E a b, U E a <> U E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = true.
Proof. intros E a b H. rewrite branch_ne_U. apply negb_true_iff, Z.eqb_neq. exact H. Qed.
(* K2: not t, p ; bltu t, n  (p + n wraps): refuted by U p + U n < 2^64 (cf. released YE2y.v:446 br_ovf_false). *)
Lemma fmt_not_ltu_not : forall E p n, U E p + U E n < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR p (SLit (-1)))) (sv_denot E n) = false.
Proof. intros E p n H. rewrite branch_ltu_U, U_not. apply Z.ltb_ge. lia. Qed.
(* K3: add s, p, n ; bltu s, p  (p + n wraps): refuted by U p + U n < 2^64. Both operand orders. *)
Lemma fmt_add_ltu_not : forall E p n, U E p + U E n < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD p n)) (sv_denot E p) = false.
Proof. intros E p n H. rewrite branch_ltu_U, (U_add2 E p n H). apply Z.ltb_ge. pose proof (U_range E n). lia. Qed.
Lemma fmt_add_ltu_not_r : forall E p n, U E p + U E n < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD n p)) (sv_denot E p) = false.
Proof. intros E p n H. rewrite branch_ltu_U, (U_add2 E n p) by lia. apply Z.ltb_ge. pose proof (U_range E n). lia. Qed.
(* K4: bltu k, p with a constant k (p near 2^64): refuted by U p <= U k. *)
Lemma fmt_ltu_not : forall E a b, U E b <= U E a -> branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b H. rewrite branch_ltu_U. apply Z.ltb_ge. exact H. Qed.
(* K5: bgeu k, p with a constant k (p - (k+1) underflows): refuted by U k < U p. *)
Lemma fmt_geu_not : forall E a b, U E a < U E b -> branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b H. rewrite branch_geu_U. apply negb_false_iff, Z.ltb_lt. exact H. Qed.
(* K6: snez x, base ; seqz y, res ; xor z, x, y ; beqz z  (pointer arithmetic changes nullness): refuted by base and
   res both nonzero. snez = sltu rd, x0, rs ; seqz = sltiu rd, rs, 1. The zero operand is any value with U = 0. *)
Lemma fmt_nullpres_not : forall E base res zr z1 o, U E zr = 0 -> U E z1 = 1 -> U E o = 0 ->
  U E base <> 0 -> U E res <> 0 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU zr base) (SAlu ALU_SLTU res z1))) (sv_denot E o) = false.
Proof.
  intros E base res zr z1 o Hzr Hz1 Ho Hb Hr. apply fmt_eq_not. rewrite Ho.
  pose proof (U_range E base). pose proof (U_range E res).
  rewrite fmt_U_xor01 by (rewrite fmt_U_sltu; destruct (_ <? _); lia).
  rewrite !fmt_U_sltu, Hzr, Hz1.
  destruct (Z.ltb_spec 0 (U E base)); destruct (Z.ltb_spec (U E res) 1); try lia; cbn; lia.
Qed.
(* K7: addiw r, s, 1 ; blt r, s  (int overflow of s + 1): refuted by s being an int32 below INT_MAX. *)
Lemma fmt_addw1_lt_not : forall E s z1, U E z1 = 1 -> - 2 ^ 31 <= Sg E s < 2 ^ 31 - 1 ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD s z1)) (sv_denot E s) = false.
Proof.
  intros E s z1 H1 Hs. rewrite fmt_br_lt, S_SAluw. cbn [zalu_raw]. rewrite H1.
  rewrite (U_S_mod E s 32) by lia. change (1 mod 2 ^ 32) with 1.
  assert (Hw : bv_swrap 32 (Sg E s mod 2 ^ 32 + 1) = Sg E s + 1).
  { rewrite (swrapN_congr 32 (Sg E s mod 2 ^ 32 + 1) (Sg E s + 1)).
    - apply swrap32_id. lia.
    - change (2 ^ Z.of_N 32) with (2 ^ 32).
      replace (Sg E s mod 2 ^ 32 + 1 - (Sg E s + 1)) with (Sg E s mod 2 ^ 32 - Sg E s) by lia.
      rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  rewrite Hw. apply Z.ltb_ge. lia.
Qed.

(* ---- tactics ---- *)
(* fm_trap_arith H: H : branch_taken _ (sv_denot E _) (sv_denot E _) = true  ~>  a Z fact over U / Sg, with the
   recognised operand shapes unfolded and every literal operand U E (SLit z) replaced by its value (z in
   [-2^64, 2^64)). Leaves U E (atom) terms for the walk's own facts. *)
Ltac fm_U_lits H :=
  repeat match type of H with
  | context [U ?E (SLit ?z)] =>
      first [ rewrite (U_lit E z) in H by lia | rewrite (fmt_U_litn E z) in H by lia ]
  end.
Ltac fm_trap_arith H :=
  first [ rewrite branch_eq_U in H | rewrite branch_ne_U in H | rewrite branch_ltu_U in H
        | rewrite branch_geu_U in H | rewrite fmt_br_lt in H | rewrite fmt_br_ge in H ];
  rewrite ?U_not, ?fmt_U_sltu in H; fm_U_lits H;
  first [ apply Z.eqb_eq in H | apply Z.ltb_lt in H
        | apply negb_true_iff in H; first [apply Z.eqb_neq in H | apply Z.ltb_ge in H]
        | idtac ].
(* fm_kill_trap H: the trap arm of a guard is impossible: from H as above and the walk's facts in context, by lia. *)
Ltac fm_kill_trap H := exfalso; fm_trap_arith H; lia.
