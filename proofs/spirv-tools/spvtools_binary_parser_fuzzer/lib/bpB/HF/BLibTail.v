(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BAgentLib BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymDriveH4 BRefMemcpyLib.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.

Lemma vadd_ZZ : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Z.add_mod by lia. apply zbv_mod.
Qed.

Lemma vsub_ZZ : forall x y, v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Zminus_mod. apply zbv_mod.
Qed.

Lemma vmul_ZZ : forall x y, v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof.
  intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Z.mul_mod by lia. apply zbv_mod.
Qed.

Lemma word_Z : forall w : word, w = Z_to_bv 64 (bv_unsigned w).
Proof. intros w. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma vadd_wZ : forall (w : word) y, v_add w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w + y).
Proof. intros w y. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_Zw : forall x (w : word), v_add (Z_to_bv 64 x) w = Z_to_bv 64 (x + bv_unsigned w).
Proof. intros x w. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_ww : forall (w w' : word), v_add w w' = Z_to_bv 64 (bv_unsigned w + bv_unsigned w').
Proof. intros. reflexivity. Qed.
Lemma vsub_wZ : forall (w : word) y, v_sub w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w - y).
Proof. intros w y. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vsub_Zw : forall x (w : word), v_sub (Z_to_bv 64 x) w = Z_to_bv 64 (x - bv_unsigned w).
Proof. intros x w. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vmul_wZ : forall (w : word) y, v_mul w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w * y).
Proof. intros w y. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.
Lemma vmul_Zw : forall x (w : word), v_mul (Z_to_bv 64 x) w = Z_to_bv 64 (x * bv_unsigned w).
Proof. intros x w. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.

Lemma ed_add : forall E a b, edenot E (EAlu ALU_ADD a b) = v_add (edenot E a) (edenot E b).
Proof. intros. cbn [edenot]. apply alu_add. Qed.
Lemma ed_sub : forall E a b, edenot E (EAlu ALU_SUB a b) = v_sub (edenot E a) (edenot E b).
Proof. intros. cbn [edenot]. apply alu_sub. Qed.
Lemma ed_mul : forall E a b, edenot E (EMd M_MUL a b) = v_mul (edenot E a) (edenot E b).
Proof. intros. cbn [edenot]. apply m_mul. Qed.

Lemma ed_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma ed_var : forall E n, edenot E (EVar n) = ev E n.
Proof. reflexivity. Qed.

Ltac not_arith t :=
  lazymatch t with
  | v_add _ _ => fail | v_sub _ _ => fail | v_mul _ _ => fail | Z_to_bv _ _ => fail
  | _ => idtac
  end.

Ltac ed_lin pins :=
  rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul; cbn [ev];
  pins;
  repeat match goal with
         | |- context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y)
         | |- context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y)
         | |- context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y)
         | |- context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y)
         | |- context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w)
         | |- context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y)
         | |- context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w)
         | |- context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y)
         | |- context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w)
         | |- context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w')
         end.

Ltac ed_lin_in H pins :=
  rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul in H; cbn [ev] in H;
  pins;
  repeat match type of H with
         | context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y) in H
         | context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y) in H
         | context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y) in H
         | context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y) in H
         | context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w) in H
         | context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y) in H
         | context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w) in H
         | context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y) in H
         | context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w) in H
         | context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w') in H
         end.

Lemma eqb_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros. unfold bv_eqb. rewrite !u_small by lia. reflexivity. Qed.
Lemma ltu_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof. intros. unfold bv_ltu. rewrite !u_small by lia. reflexivity. Qed.
Lemma lts_ZZ : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !bv_signed_small; rewrite ?u_small; try lia.
  all: change (bv_half_modulus 64) with (2 ^ 63)%Z; lia.
Qed.

Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_small z) by lia
      end
  end.

Lemma rdn_app_Z : forall segs m a n1 n2 b1 b2,
  rdn segs m (Z_to_bv 64 a) n1 = Some b1 ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some b2 ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 a) (n1 + n2) = Some (b1 ++ b2).
Proof.
  intros segs m a n1 n2 b1 b2 H1 H2 Ha Hn.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Lemma vals_ev_junk : forall vals R i, (i < 32)%nat ->
  vals_ev (vals ++ junk_vals R) (length vals + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros vals R i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals.
  rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

Lemma v_addiw_id_errno : forall x : word,
  (2 ^ 64 - 4095 <= bv_unsigned x)%Z -> v_addiw x 0 = x.
Proof.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  intros x Hx. pose proof (u64_range x) as Hr. unfold v_addiw. rewrite Z.add_0_r.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  replace ((bv_unsigned x + 2 ^ 31) mod 2 ^ 32)%Z with (bv_unsigned x + 2 ^ 31 - 2 ^ 64)%Z by
    (apply Z.mod_unique with (q := (2 ^ 32)%Z); lia).
  symmetry. apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma rdn_byte_Z : forall segs m a n bs j,
  rdn segs m (Z_to_bv 64 a) n = Some bs -> (j < n)%nat -> (0 <= a)%Z -> (a + Z.of_nat j < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m a n bs j H Hj Ha Hn.
  pose proof (rdn_nth segs m n (Z_to_bv 64 a) bs j H Hj) as R. rewrite w_add_nat, u_small in R by lia. exact R.
Qed.

Lemma nth_app_l : forall {A} (l l' : list A) (d : A) j, (j < length l)%nat -> nth j (l ++ l') d = nth j l d.
Proof. intros. apply app_nth1. assumption. Qed.

Lemma In_nth_neq : forall {A} (l : list A) (x d : A) j, ~ In x l -> (j < length l)%nat -> nth j l d <> x.
Proof. intros A l x d j Hn Hj E. apply Hn. rewrite <- E. apply nth_In. exact Hj. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
