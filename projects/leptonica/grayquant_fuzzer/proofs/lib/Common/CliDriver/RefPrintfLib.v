(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec SeqExec AgentLib.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma alu_add_Z : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 a + Z_to_bv 64 b)%bv.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma alu_and3_Z : forall a, 0 <= a ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (a mod 4).
Proof.
  intros a Ha. apply bv_eq.
  change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 3)).
  rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2 ^ 2) with 4.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
Qed.
End VP2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_eq0_Z : forall a, 0 <= a < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 0) = (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
End VP3.

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_ne0_Z : forall a, 0 <= a < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 0) = negb (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
End VP4.

(* [comment removed for export] *)
Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_and3 : forall c (w k : Z) (t : bool), 0 <= w + k ->
  match c with BC_EQ => ((w + k) mod 4 =? 0) = t | BC_NE => negb ((w + k) mod 4 =? 0) = t | _ => False end ->
  branch_taken c (alu64 ALU_AND (alu64 ALU_ADD (Z_to_bv 64 w) (Z_to_bv 64 k)) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
  intros c w k t Hw Hc. rewrite alu_add_Z, alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound (w + k) 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_and3_0 : forall c (w : Z) (t : bool), 0 <= w ->
  match c with BC_EQ => (w mod 4 =? 0) = t | BC_NE => negb (w mod 4 =? 0) = t | _ => False end ->
  branch_taken c (alu64 ALU_AND (Z_to_bv 64 w) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
  intros c w t Hw Hc. rewrite alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound w 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.
End VP6.

(* [comment removed for export] *)
Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_2 : forall segs m (a : word) b0 b1,
  (bv_unsigned a + 2 <= 2 ^ 64)%Z ->
  rdn segs m a 1 = Some [b0] -> rdn segs m (Z_to_bv 64 (bv_unsigned a + 1)) 1 = Some [b1] ->
  rdn segs m a 2 = Some [b0; b1].
Proof.
  intros segs m a b0 b1 Hnw H0 H1. cbn [rdn] in *.
  destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x|]; [|discriminate].
  injection H0 as ->.
  replace (a + 1)%bv with (Z_to_bv 64 (bv_unsigned a + 1)).
  2:{ apply bv_eq. rewrite u64_lit by (pose proof (u64_range a); lia). symmetry. apply u_add1. lia. }
  destruct (match m (Z_to_bv 64 (bv_unsigned a + 1)) with Some b => Some b | None => seg_rom segs _ end) as [y|];
    [|discriminate].
  injection H1 as ->. reflexivity.
Qed.
End VP7.

(* [comment removed for export] *)
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma lin_neg1_val : forall (x : word) c,
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c) = Z_to_bv 64 (c - bv_unsigned x).
Proof.
  intros x c. apply bv_eq.
  change (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c))
    with ((Z_to_bv 64 (-1) * x) + Z_to_bv 64 c)%bv.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  rewrite <- Z.add_mod by lia.
  replace ((2 ^ 64 - 1) * bv_unsigned x + c) with ((c - bv_unsigned x) + bv_unsigned x * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
End VP8.

Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_geu_Z : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Hab Ha. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
End VP9.

Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_geu_Z_false : forall a b, 0 <= a < b -> b < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b Hab Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
End VP10.

Section VP11. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bt_ltu_Z : forall a b (t : bool), 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  (a <? b) = t -> branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = t.
Proof. intros a b t Ha Hb Ht. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia. exact Ht. Qed.
End VP11.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section VP12. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma mod4_shift : forall w k r, w mod 4 = r -> (w + k) mod 4 = (r + k) mod 4.
Proof. intros w k r H. rewrite <- Zplus_mod_idemp_l, H. reflexivity. Qed.
End VP12.

Section VP13. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma even_mod4 : forall w, w mod 2 = 0 -> w mod 4 = 0 \/ w mod 4 = 2.
Proof. intros w H. lia. Qed.
End VP13.

Section VP14. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma mod4_cases : forall w, w mod 4 = 0 \/ w mod 4 = 1 \/ w mod 4 = 2 \/ w mod 4 = 3.
Proof. intros w. lia. Qed.
End VP14.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
