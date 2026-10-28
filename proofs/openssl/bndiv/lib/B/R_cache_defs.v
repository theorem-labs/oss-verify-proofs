(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout R_small R_m2s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition INST : Z := g_instance.                       (* [comment removed for export] *)
Definition i_spacebeg : Z := g_instance + 32.            (* [comment removed for export] *)
Definition i_rtoi : Z := g_instance + 40.                (* [comment removed for export] *)
Definition i_regioninfo : Z := g_instance + 48.          (* [comment removed for export] *)
Definition i_premapped : Z := g_instance + 56.           (* [comment removed for export] *)

Definition cacheT (T : Z) : Z := T + 208.                (* [comment removed for export] *)
Definition pc_addr (T c : Z) : Z := T + 208 + 80 * c.    (* [comment removed for export] *)
Definition cstats (T : Z) : Z := T + 2768.               (* [comment removed for export] *)
Definition cstat_alloc (T : Z) : Z := T + 2784.          (* [comment removed for export] *)
Definition cstat_mapped (T : Z) : Z := T + 2792.         (* [comment removed for export] *)
Definition astats (T : Z) : Z := T + 2800.               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pc_cells (m : mem) (P cnt mc cs : Z) : Prop :=
  rw_cells bsegs m P [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

(* [comment removed for export] *)
Definition cptr (w : word) : Z := bv_unsigned w mod 2^32.
(* [comment removed for export] *)
Definition chunk_addr (SB c : Z) (w : word) : Z := SB + c * 2^32 + 16 * cptr w.

(* [comment removed for export] *)
Definition img_hull_lo : Z := 0x10000.
Definition img_hull_hi : Z := 0xbfd000.

(* [comment removed for export] *)
Definition T_ok (ACEIL T : Z) : Prop :=
  0 < T /\ T mod 4096 = 0 /\ T + 4096 <= ACEIL /\ ACEIL <= 2^47
  /\ (T + 4096 <= img_hull_lo \/ img_hull_hi <= T).

(* [comment removed for export] *)
Definition SB_ok (ACEIL SB : Z) : Prop :=
  kHighShadowEnd < SB /\ SB mod 2^16 = 0 /\ SB + 2^37 + 4096 <= ACEIL /\ ACEIL <= 2^47.

Lemma T_ok_range : forall ACEIL T, T_ok ACEIL T -> 0 < T /\ T + 4096 <= 2^47.
Proof. intros ACEIL T (H1 & _ & H3 & H4 & _). lia. Qed.

Lemma SB_ok_range : forall ACEIL SB, SB_ok ACEIL SB -> kHighShadowEnd < SB /\ SB + 2^37 + 4096 <= 2^47.
Proof. intros ACEIL SB (H1 & _ & H3 & H4). lia. Qed.

(* [comment removed for export] *)
Lemma cptr_range : forall w, 0 <= cptr w < 2^32.
Proof. intros w. unfold cptr. apply Z.mod_pos_bound. lia. Qed.

Lemma zx32_cptr : forall w, Z.land (bv_unsigned w) (2^32 - 1) = cptr w.
Proof.
  intros w. unfold cptr. rewrite <- Z.land_ones by lia. reflexivity.
Qed.

Lemma nth_error_ex : forall {X} (l : list X) (i : nat), (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
  intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Ltac solve_cond_u := unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac ifT :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond_u]
  end.
Ltac ifF :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond_u]
  end.

Lemma shl32_shr30 : forall x, (0 <= x < 2^32)%Z -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 30 = (4 * x)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 32)%Z with ((4 * x) * 2 ^ 30)%Z by lia. apply Z.div_mul. lia.
Qed.

Lemma shl32_shr32 : forall x, (0 <= x < 2^32)%Z -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma swrap32_small : forall x, (0 <= x < 2^31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma wrap32_small : forall x, (0 <= x < 2^32)%Z -> bv_wrap 32 x = x.
Proof. intros x Hx. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma srliw1_small : forall x, (0 <= x < 2^31)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 1) = (x / 2)%Z.
Proof.
  intros x Hx. rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  apply swrap32_small. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Lemma v_divuw_small : forall x y, (0 <= x < 2^31)%Z -> (0 < y < 2^31)%Z ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia. rewrite !wrap32_small by lia.
  rewrite (proj2 (Z.eqb_neq y 0)) by lia. f_equal. apply swrap32_small.
  split; [apply Z.div_pos; lia| apply (Z.le_lt_trans _ x); [apply Z.div_le_upper_bound; nia| lia]].
Qed.

(* [comment removed for export] *)
Ltac solve_cond_w := unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; rewrite ?Z_to_bv_unsigned;
  unfold bv_wrap, bv_modulus; cbn [Z.of_N]; solve_cond_rec.
Ltac ifTw :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond_w]
  end.
Ltac ifFw :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond_w]
  end.

Lemma zx32_small : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
