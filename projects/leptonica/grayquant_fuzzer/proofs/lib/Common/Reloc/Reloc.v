(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rl (d c : Z) : word := Z_to_bv 64 (c + d).
Arguments rl : simpl never.

Lemma rl_unfold : forall d c, rl d c = Z_to_bv 64 (c + d).
Proof. reflexivity. Qed.

Lemma Z_to_bv64_mod_eq : forall a b : Z, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma rl_u_mod : forall d c, bv_unsigned (rl d c) = (c + d) mod 2^64.
Proof. intros. unfold rl. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rl_u : forall d c, 0 <= c + d < 2^64 -> bv_unsigned (rl d c) = c + d.
Proof. intros d c H. rewrite rl_u_mod. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma rl_addi : forall d c e, v_addi (rl d c) e = rl d (c + e).
Proof.
  intros d c e. unfold v_addi. rewrite rl_u_mod. unfold rl. apply Z_to_bv64_mod_eq.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rl_btgt : forall d c e, btgt (rl d c) e = rl d (c + e).
Proof. intros. unfold btgt. apply rl_addi. Qed.

Lemma rl_at : forall d c e, at_ (rl d c) e = rl d (c + e).
Proof. intros. exact (rl_addi d c e). Qed.

Lemma rl_auipc : forall d c e, v_auipc (rl d c) e = rl d (c + e).
Proof.
  intros d c e. unfold v_auipc. rewrite rl_u_mod. unfold rl. apply Z_to_bv64_mod_eq.
  rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma rl_add_r : forall d c k, v_add (rl d c) (Z_to_bv 64 k) = rl d (c + k).
Proof.
  intros d c k. unfold v_add. rewrite rl_u_mod, Z_to_bv_unsigned. unfold rl. apply Z_to_bv64_mod_eq.
  change (bv_wrap 64 k) with (k mod 2^64). rewrite <- Zplus_mod. f_equal. lia.
Qed.

Lemma rl_add_l : forall d c k, v_add (Z_to_bv 64 k) (rl d c) = rl d (c + k).
Proof.
  intros d c k. unfold v_add. rewrite rl_u_mod, Z_to_bv_unsigned. unfold rl. apply Z_to_bv64_mod_eq.
  change (bv_wrap 64 k) with (k mod 2^64). rewrite <- Zplus_mod. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rl_sub_same : forall d c1 c2, v_sub (rl d c1) (rl d c2) = Z_to_bv 64 (c1 - c2).
Proof.
  intros d c1 c2. unfold v_sub. rewrite !rl_u_mod. apply Z_to_bv64_mod_eq.
  rewrite <- Zminus_mod. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rl_even_u : forall d c, (c + d) mod 2 = 0 -> bv_unsigned (rl d c) mod 2 = 0.
Proof.
  intros d c H. rewrite rl_u_mod. change (2^64) with (2 * 2^63).
  rewrite Z.rem_mul_r by lia. rewrite H. 
  rewrite Z.add_0_l. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma rl_ret_ok : forall d c, (c + d) mod 2 = 0 -> ret_ok (rl d c).
Proof. intros d c H. apply ret_ok_even. apply rl_even_u. exact H. Qed.

(* [comment removed for export] *)
Lemma fetch_even : forall segs (a : word) w, fetch_word segs a = Some w -> bv_unsigned a mod 2 = 0.
Proof.
  intros segs a w H. unfold fetch_word in H.
  destruct (Z.eqb (bv_unsigned a mod 2) 0) eqn:E; cbn [negb] in H; [apply Z.eqb_eq in E; exact E | discriminate H].
Qed.

Lemma fetch_ret_ok : forall segs (a : word) w, fetch_word segs a = Some w -> ret_ok a.
Proof. intros segs a w H. apply ret_ok_even. exact (fetch_even segs a w H). Qed.

Lemma rl_jalr0 : forall d c, ret_ok (rl d c) -> v_jalr (rl d c) 0 = rl d c.
Proof. intros d c H. exact H. Qed.

(* [comment removed for export] *)
Lemma rl_jalr_fetch : forall segs d c e c' w, c + e = c' ->
  fetch_word segs (rl d c') = Some w -> v_jalr (rl d c) e = rl d c'.
Proof.
  intros segs d c e c' w <- Hf. pose proof (fetch_even _ _ _ Hf) as Hev. rewrite rl_u_mod in Hev.
  unfold v_jalr, jalr_tgtZ. rewrite rl_u_mod.
  assert (E : ((c + d) mod 2^64 + e) mod 2 = 0).
  { change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  rewrite land_m2_even by exact E. unfold rl. apply Z_to_bv64_mod_eq.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rl_addi_lit : forall d c e c', c + e = c' -> v_addi (rl d c) e = rl d c'.
Proof. intros d c e c' <-. apply rl_addi. Qed.
Lemma rl_btgt_lit : forall d c e c', c + e = c' -> btgt (rl d c) e = rl d c'.
Proof. intros d c e c' <-. apply rl_btgt. Qed.
Lemma rl_auipc_lit : forall d c e c', c + e = c' -> v_auipc (rl d c) e = rl d c'.
Proof. intros d c e c' <-. apply rl_auipc. Qed.
Lemma rl_at_lit : forall d c e c', c + e = c' -> at_ (rl d c) e = rl d c'.
Proof. intros d c e c' <-. apply rl_at. Qed.
Lemma rl_num_lit : forall d c c', c = c' -> rl d c = rl d c'.
Proof. intros d c c' <-. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rl_eqb_same : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 ->
  c_eq (rl d c1) (rl d c2) = (c1 =? c2).
Proof.
  intros d c1 c2 H1 H2. unfold c_eq, bv_eqb. rewrite !rl_u by assumption.
  destruct (Z.eqb_spec c1 c2) as [->|N]; [apply Z.eqb_refl | apply Z.eqb_neq; lia].
Qed.

Lemma rl_ltu_same : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 ->
  c_ltu (rl d c1) (rl d c2) = (c1 <? c2).
Proof.
  intros d c1 c2 H1 H2. unfold c_ltu, bv_ltu. rewrite !rl_u by assumption.
  destruct (Z.ltb_spec c1 c2) as [L|L]; [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma rl_inj : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 -> rl d c1 = rl d c2 -> c1 = c2.
Proof.
  intros d c1 c2 H1 H2 E. apply (f_equal bv_unsigned) in E. rewrite !rl_u in E by assumption. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint dlookup (t : list (positive * Z)) (b : positive) : Z :=
  match t with
  | [] => 0
  | (b', d) :: t' => if Pos.eqb b b' then d else dlookup t' b
  end.

(* [comment removed for export] *)
Fixpoint slookup (t : list (Z * Z)) (c : Z) : Z :=
  match t with
  | [] => 0
  | (c', w) :: t' => if Z.eqb c c' then w else slookup t' c
  end.

(* [comment removed for export] *)
Definition DELTA_LO : Z := - 2^16.
Definition DELTA_HI : Z := 2^32.
Definition dtab_ok (t : list (positive * Z)) : bool :=
  forallb (fun bd => (DELTA_LO <=? snd bd) && (snd bd <=? DELTA_HI)) t.

Class Reloc := {
  rl_segs : list Segment;              (* [comment removed for export] *)
  rl_dtab : list (positive * Z);       (* [comment removed for export] *)
  rl_stab : list (Z * Z);              (* [comment removed for export] *)
  rl_img_lo : Z;                       (* [comment removed for export] *)
  rl_rw_lo : Z;                        (* [comment removed for export] *)
  rl_img_hi : Z;
  rl_dtab_ok : dtab_ok rl_dtab = true
}.

Definition rl_delta {RL : Reloc} (b : positive) : Z := dlookup rl_dtab b.
Arguments rl_delta : simpl never.

Lemma dlookup_bd : forall t b, dtab_ok t = true -> DELTA_LO <= dlookup t b <= DELTA_HI.
Proof.
  induction t as [|[b' d] t IH]; intros b H; cbn [dlookup].
  - unfold DELTA_LO, DELTA_HI. lia.
  - cbn [dtab_ok forallb snd] in H. apply andb_prop in H as [H1 H2].
    destruct (Pos.eqb b b').
    + apply andb_prop in H1 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb. lia.
    + apply IH. exact H2.
Qed.

Lemma rl_delta_bd : forall {RL : Reloc} b, - 2^16 <= rl_delta b <= 2^32.
Proof. intros RL b. exact (dlookup_bd rl_dtab b rl_dtab_ok). Qed.

(* [comment removed for export] *)
Lemma rl_delta_u : forall {RL : Reloc} b c, 2^16 <= c < 2^63 -> bv_unsigned (rl (rl_delta b) c) = c + rl_delta b.
Proof. intros RL b c Hc. pose proof (rl_delta_bd b). apply rl_u. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rl_fold_by p d c e L :=
  let c' := vm_eval (c + e)%Z in
  replace p with (rl d c') by (first [ exact (L d c e c' eq_refl) | symmetry; exact (L d c e c' eq_refl) ]).

Ltac rl_pc p :=
  lazymatch p with
  | rl ?d ?c => tryif is_Z_lit c then idtac
                else (let c' := vm_eval c in
                      replace p with (rl d c') by (first [ reflexivity | symmetry; reflexivity ]))
  | v_addi (rl ?d ?c) ?e => rl_fold_by p d c e rl_addi_lit
  | btgt (rl ?d ?c) ?e => rl_fold_by p d c e rl_btgt_lit
  | v_auipc (rl ?d ?c) ?e => rl_fold_by p d c e rl_auipc_lit
  | at_ (rl ?d ?c) ?e => rl_fold_by p d c e rl_at_lit
  | v_jalr (rl ?d ?c) ?e =>
      let c' := vm_eval (c + e)%Z in
      first [ match goal with
              | H : fetch_word _ (rl d c') = Some _ |- _ => rewrite (rl_jalr_fetch _ d c e c' _ eq_refl H)
              | H : ret_ok (rl d c) |- _ =>
                  lazymatch e with 0%Z => rewrite (H : v_jalr (rl d c) 0 = rl d c) end
              end
            | idtac ]
  end.

#[export] Ltac norm_pc_state st ::=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => first [ rl_pc p | wlit p ]
       | _ => idtac
       end.

(* [comment removed for export] *)
Ltac rl_val v :=
  lazymatch v with
  | v_addi (rl ?d ?c) ?e => rl_fold_by v d c e rl_addi_lit
  | v_auipc (rl ?d ?c) ?e => rl_fold_by v d c e rl_auipc_lit
  | at_ (rl ?d ?c) ?e => rl_fold_by v d c e rl_at_lit
  | btgt (rl ?d ?c) ?e => rl_fold_by v d c e rl_btgt_lit
  end.

#[export] Ltac vals_lit ::=
  repeat match goal with
         | |- context [regupd _ _ ?v] => first [ val_lit v | rl_val v ]
         end.

(* [comment removed for export] *)
Ltac rl_norm :=
  repeat match goal with
         | |- context [v_addi (rl ?d ?c) ?e] => rl_val (v_addi (rl d c) e)
         | |- context [v_auipc (rl ?d ?c) ?e] => rl_val (v_auipc (rl d c) e)
         | |- context [at_ (rl ?d ?c) ?e] => rl_val (at_ (rl d c) e)
         | |- context [btgt (rl ?d ?c) ?e] => rl_val (btgt (rl d c) e)
         end.

(* [comment removed for export] *)
Ltac rl_bounds :=
  repeat match goal with
         | |- context [@rl_delta ?RL ?b] =>
             lazymatch goal with
             | _ : - 2^16 <= @rl_delta RL b <= 2^32 |- _ => fail
             | _ => pose proof (@rl_delta_bd RL b)
             end
         end.
Ltac rl_unorm :=
  repeat match goal with
         | |- context [bv_unsigned (rl (@rl_delta ?RL ?b) ?c)] =>
             rewrite (@rl_delta_u RL b c) by lia
         end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rl_to_Z_in H :=
  repeat match type of H with
         | context [rl ?d ?c] =>
             let z := vm_eval (c + d)%Z in
             change (rl d c) with (Z_to_bv 64 z) in H
         end.

Ltac bvlit64_to_Z_in H :=
  repeat match type of H with
         | context [@BV 64 ?z ?p] =>
             replace (@BV 64 z p) with (Z_to_bv 64 z) in H by (apply bv_eq; vm_compute; reflexivity)
         end.
Ltac bvlit64_to_Z :=
  repeat match goal with
         | |- context [@BV 64 ?z ?p] =>
             replace (@BV 64 z p) with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity)
         end.

Ltac rl_tail t :=
  let H := fresh "RLT" in
  pose proof t as H;
  rl_to_Z_in H; bvlit64_to_Z_in H; bvlit64_to_Z;
  exact H.
