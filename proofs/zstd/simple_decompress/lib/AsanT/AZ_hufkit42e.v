(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition LB (p : Z) (z : Z) : Prop := exists i, 0 <= i <= p /\ Z.testbit z i = true.
Definition LBW (p : Z) (w : word) : Prop := LB p (bv_unsigned w).

Lemma lb_nz : forall p z, LB p z -> z <> 0.
Proof. intros p z (i & Hi & Hb) E. subst z. rewrite Z.bits_0 in Hb. discriminate Hb. Qed.

Lemma lb_mono : forall p q z, LB p z -> p <= q -> LB q z.
Proof. intros p q z (i & Hi & Hb) Hpq. exists i. split; [lia | exact Hb]. Qed.

Lemma lb_shl : forall p s z, LB p z -> 0 <= s -> p + s <= 63 -> LB (p + s) ((z * 2 ^ s) mod 2 ^ 64).
Proof.
  intros p s z (i & Hi & Hb) Hs Hps. exists (i + s). split; [lia|].
  rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mul_pow2_bits by lia.
  replace (i + s - s) with i by lia. exact Hb.
Qed.

Lemma lb_shl_le : forall p s t z, LB p z -> 0 <= t <= s -> p + s <= 63 -> LB (p + s) ((z * 2 ^ t) mod 2 ^ 64).
Proof.
  intros p s t z H Ht Hps. apply (lb_mono (p + t)); [|lia]. apply lb_shl; [exact H | lia | lia].
Qed.

Lemma lb_or1 : forall z, LB 0 (Z.lor z 1).
Proof.
  intros z. exists 0. split; [lia|]. rewrite Z.lor_spec.
  replace (Z.testbit 1 0) with true by reflexivity. apply Bool.orb_true_r.
Qed.

(* [comment removed for export] *)
Lemma lb_of_mod : forall k z, 0 <= k -> z mod 2 ^ (k + 1) <> 0 -> LB k z.
Proof.
  intros k z Hk Hz.
  assert (P : 0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound z (2 ^ (k + 1)) P) as R.
  remember (z mod 2 ^ (k + 1)) as r eqn:Er.
  assert (Hr : 0 < r) by lia.
  assert (HL : Z.log2 r < k + 1) by (apply Z.log2_lt_pow2; lia).
  exists (Z.log2 r). split; [split; [apply Z.log2_nonneg | lia]|].
  rewrite <- (Z.mod_pow2_bits_low z (k + 1) (Z.log2 r)) by lia. rewrite <- Er. apply Z.bit_log2. lia.
Qed.

Lemma lb_to_mod : forall k z, 0 <= k -> LB k z -> z mod 2 ^ (k + 1) <> 0.
Proof.
  intros k z Hk (i & Hi & Hb) E.
  assert (X : Z.testbit (z mod 2 ^ (k + 1)) i = true) by (rewrite Z.mod_pow2_bits_low by lia; exact Hb).
  rewrite E, Z.bits_0 in X. discriminate X.
Qed.

Lemma lb_of_mod512 : forall z, z mod 512 <> 0 -> LB 8 z.
Proof. intros z H. apply lb_of_mod; [lia|]. change (2 ^ (8 + 1)) with 512. exact H. Qed.

Lemma lb_to_mod512 : forall z, LB 8 z -> z mod 512 <> 0.
Proof. intros z H. change 512 with (2 ^ (8 + 1)). apply lb_to_mod; [lia | exact H]. Qed.

(* [comment removed for export] *)
Lemma lbw_nz : forall p (x : word), LBW p x -> bv_unsigned x <> 0.
Proof. intros p x H. exact (lb_nz p _ H). Qed.

Lemma lbw_pos : forall p (x : word), LBW p x -> 1 <= bv_unsigned x < 2 ^ 64.
Proof.
  intros p x H. pose proof (lbw_nz p x H). pose proof (bv_unsigned_in_range 64 x) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R. lia.
Qed.

Lemma lbw_Z : forall p z, 0 <= z < 2 ^ 64 -> LB p z -> LBW p (Z_to_bv 64 z).
Proof. intros p z Hz H. unfold LBW. rewrite u_small by lia. exact H. Qed.

Lemma lbw_unZ : forall p (x : word), LBW p x -> LB p (bv_unsigned x).
Proof. intros p x H. exact H. Qed.

Lemma lbw_mono : forall p q (x : word), LBW p x -> p <= q -> LBW q x.
Proof. intros p q x H Hpq. exact (lb_mono p q _ H Hpq). Qed.

(* [comment removed for export] *)
Lemma lbw_sll : forall p s (x y : word), LBW p x -> bv_unsigned y mod 64 <= s -> p + s <= 63 -> LBW (p + s) (alu64 ALU_SLL x y).
Proof.
  intros p s x y H Hy Hps. unfold LBW. rewrite u_sll64.
  pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as R.
  apply (lb_shl_le p s (bv_unsigned y mod 64)); [exact H | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma lbw_or1 : forall x : word, LBW 0 (alu64 ALU_OR x (Z_to_bv 64 1)).
Proof. intros x. unfold LBW. rewrite u_or64, u_small by lia. apply lb_or1. Qed.

(* [comment removed for export] *)
Lemma lbw_reload : forall (x y : word), bv_unsigned y mod 64 <= 7 -> LBW 7 (alu64 ALU_SLL (alu64 ALU_OR x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hy. change (LBW 7) with (LBW (0 + 7)). apply lbw_sll; [apply lbw_or1 | exact Hy | lia].
Qed.

(* [comment removed for export] *)
Definition EVENW (w : word) : Prop := Z.testbit (bv_unsigned w) 0 = false.

Lemma evenw_add : forall x y : word, EVENW x -> EVENW y -> EVENW (alu64 ALU_ADD x y).
Proof.
  intros x y Hx Hy. unfold EVENW in *. rewrite u_add64. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.add_bit0, Hx, Hy. reflexivity.
Qed.

Lemma evenw_mul_l : forall c (y : word), 0 <= c < 2 ^ 64 -> Z.testbit c 0 = false -> EVENW (mul_div M_MUL (Z_to_bv 64 c) y).
Proof.
  intros c y Hc He. unfold EVENW. rewrite u_mul64, (u_small c) by lia. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.bit0_eqb in He. apply Z.eqb_neq in He. pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as R.
  replace c with (2 * (c / 2)) by lia. rewrite <- Z.mul_assoc. apply Z.testbit_even_0.
Qed.

Lemma evenw_and_m2 : forall x : word, EVENW (alu64 ALU_AND x (Z_to_bv 64 (-2))).
Proof.
  intros x. unfold EVENW. rewrite u_and64. rewrite Z.land_spec.
  replace (Z.testbit (bv_unsigned (Z_to_bv 64 (-2))) 0) with false by (vm_compute; reflexivity). apply Bool.andb_false_r.
Qed.

Lemma lbw_add1 : forall x : word, EVENW x -> LBW 0 (alu64 ALU_ADD x (Z_to_bv 64 1)).
Proof.
  intros x Hx. unfold LBW, LB. exists 0. split; [lia|]. rewrite u_add64, (u_small 1) by lia.
  rewrite Z.mod_pow2_bits_low by lia. rewrite Z.add_bit0, Hx. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lbw_reload2 : forall (x y : word), EVENW x -> bv_unsigned y mod 64 <= 7 -> LBW 7 (alu64 ALU_SLL (alu64 ALU_ADD x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hx Hy. change (LBW 7) with (LBW (0 + 7)). apply lbw_sll; [apply lbw_add1; exact Hx | exact Hy | lia].
Qed.

(* [comment removed for export] *)
Lemma land7_mod64 : forall c : word, bv_unsigned (alu64 ALU_AND c (Z_to_bv 64 7)) mod 64 <= 7.
Proof.
  intros c. rewrite u_and64, (u_small 7) by lia.
  pose proof (bv_unsigned_in_range 64 c) as R.
  assert (H : 0 <= Z.land (bv_unsigned c) 7 <= 7)
    by (split; [apply Z.land_nonneg; right; lia | apply land_le_r; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma land7z_mod64 : forall c : Z, 0 <= c -> Z.land c 7 mod 64 <= 7.
Proof.
  intros c Hc.
  assert (H : 0 <= Z.land c 7 <= 7) by (split; [apply Z.land_nonneg; right; lia | apply land_le_r; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac e42_amt :=
  cbn [edenot];
  rewrite ?u_add64, ?u_mul64; rewrite ?(u_small 256) by lia;
  lazymatch goal with
  | |- context [bv_unsigned (ev ?E ?j)] => idtac
  | |- ?G => fail 1 "e42_amt: unexpected amount" G
  end;
  (* [comment removed for export] *)
  repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end;
  repeat match goal with
  | |- context [bv_unsigned (ev ?E ?j)] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
      | _ => let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
      end
  end;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac e42_lb_atom KXA :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EVar ?a)) =>
      change (LBW p (ev E a)); rewrite (KXA a) by (cbn [length]; lia); cbn [znth nth]; rewrite ?Z_to_bv_bv_unsigned;
      first [ assumption | eapply lbw_mono; [eassumption | lia] | lazymatch goal with |- ?G => fail 1 "e42_lb_atom:" G end ]
  end.

(* [comment removed for export] *)
Ltac e42_lb_chain KXA :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL ?a ?b)) =>
      change (LBW p (alu64 ALU_SLL (edenot E a) (edenot E b)));
      let q := eval vm_compute in (p - 11) in
      change p with (q + 11);
      apply (lbw_sll q 11 (edenot E a) (edenot E b)); [e42_lb_chain KXA | e42_amt | lia ]
  | |- LBW ?p (edenot ?E (EVar ?a)) => e42_lb_atom KXA
  | |- ?G => fail 1 "e42_lb_chain: unexpected goal" G
  end.

(* [comment removed for export] *)
Ltac e42_even :=
  lazymatch goal with
  | |- EVENW (edenot ?E (EAlu ALU_ADD ?a ?b)) =>
      change (EVENW (alu64 ALU_ADD (edenot E a) (edenot E b))); apply evenw_add; e42_even
  | |- EVENW (edenot ?E (EMd M_MUL (ELit ?c) ?b)) =>
      change (EVENW (mul_div M_MUL (Z_to_bv 64 c) (edenot E b))); apply evenw_mul_l; [lia | reflexivity]
  | |- EVENW (edenot ?E (EAlu ALU_AND ?a (ELit (-2)))) =>
      change (EVENW (alu64 ALU_AND (edenot E a) (Z_to_bv 64 (-2)))); apply evenw_and_m2
  | |- ?G => fail 1 "e42_even: unexpected term" G
  end.

(* [comment removed for export] *)
Ltac e42_lb_reload :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?x (ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_ADD (edenot E x) (Z_to_bv 64 1)) (edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload2;
      [ e42_even
      | lazymatch c with
        | EAlu ALU_AND ?v (ELit 7) => change (edenot E c) with (alu64 ALU_AND (edenot E v) (Z_to_bv 64 7)); apply land7_mod64
        | _ => cbn [edenot]; rewrite ?u_and64; rewrite ?(u_small 7) by lia; Z.div_mod_to_equations; lia
        end ]
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL (EAlu ALU_OR ?x (ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_OR (edenot E x) (Z_to_bv 64 1)) (edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload;
      lazymatch c with
      | EAlu ALU_AND ?v (ELit 7) => change (edenot E c) with (alu64 ALU_AND (edenot E v) (Z_to_bv 64 7)); apply land7_mod64
      | _ => cbn [edenot]; rewrite ?u_and64; rewrite ?(u_small 7) by lia; Z.div_mod_to_equations; lia
      end
  | |- ?G => fail 1 "e42_lb_reload: unexpected term" G
  end.

