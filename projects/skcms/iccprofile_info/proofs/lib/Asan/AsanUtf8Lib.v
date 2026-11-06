(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk Frame WalkTac RefMemcpyLib
  Utf8Lib AsanUtf8Spec.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Lemma v_srli3 : forall x, 0 <= x < 2 ^ 64 -> v_srli (Z_to_bv 64 x) 3 = Z_to_bv 64 (x / 8).
Proof.
  intros x Hx. unfold v_srli. rewrite u_Z2bv by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma v_andi7 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) 7 = Z_to_bv 64 (x mod 8).
Proof.
  intros x Hx. rewrite v_andi_Z by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_lb_sbyte : forall k : byte, v_lb k = Z_to_bv 64 (sbyte k).
Proof. intros k. reflexivity. Qed.

Lemma sbyte_range : forall k : byte, -128 <= sbyte k < 128.
Proof.
  intros k. unfold sbyte, bv_signed. pose proof (bv_swrap_in_range 8 (bv_unsigned k) ltac:(discriminate)) as H.
  change (bv_half_modulus 8) with 128 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma eqb_s0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. destruct (Z.lt_ge_cases x 0).
  - rewrite eqb_neg0 by lia. symmetry. apply Z.eqb_neq. lia.
  - rewrite eqb_ZZ by lia. reflexivity.
Qed.

Lemma divmod8 : forall x, 0 <= x -> 0 <= x / 8 <= x /\ 0 <= x mod 8 < 8 /\ x = 8 * (x / 8) + x mod 8.
Proof.
  intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_pos x 8 Hx ltac:(lia)). lia.
Qed.
End WithFP1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac sn F D := idtac; stepn F D.
Ltac run_to tac := eapply fin_steps; [ tac; apply mst_refl | ].
Ltac run_ret tac := eapply fin_ret; [ tac; apply mst_refl | ].

(* [comment removed for export] *)
Ltac fbr F D :=
  eapply fin_branch;
  [ exact F | reflexivity | exact D | gres; reflexivity | gres; reflexivity
  | cbn [branch_taken]; rwH; intros ?Hc; wlits | cbn [branch_taken]; rwH; intros ?Hc; wlits ].

(* [comment removed for export] *)
Ltac condZ :=
  repeat match goal with
    | H : context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 0)] |- _ => rewrite (eqb_s0 x) in H by lia
    | H : context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] |- _ => rewrite (eqb_ZZ x y) in H by lia
    | H : context [bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] |- _ => rewrite (lts_ZZ x y) in H by lia
    | H : context [bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] |- _ => rewrite (ltu_ZZ x y) in H by lia
    end.

(* [comment removed for export] *)
Ltac decide_cmp :=
  match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
  end.
Ltac condD :=
  rwH; unfold c_eq, c_ltu, c_lts;
  first
    [ apply eqb_neg0; lia
    | first [ rewrite eqb_s0 by lia | rewrite eqb_ZZ by lia | rewrite ltu_ZZ by lia | rewrite lts_ZZ by lia
            | rewrite eqb_wZ by lia | rewrite ltu_wZ by lia | rewrite ltu_Zw by lia ];
      first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge ]; lia ].
Ltac btk F D := idtac; stepb_tk F D ltac:(condD).
Ltac bft F D := idtac; stepb_ft F D ltac:(condD).

(* [comment removed for export] *)
Ltac mld F D vv HS :=
  chain_step; [reflexivity
    | eapply step_ld with (v := vv);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0, ?v_addi_Z;
        first [ exact HS
              | lazymatch goal with |- rdn _ _ ?a _ = _ =>
                  lazymatch type of HS with rdn _ _ ?c _ = _ =>
                    replace a with c by (first [f_equal; lia | apply bv_eq; reflexivity]) end end;
                exact HS ]
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vnorm.

(* [comment removed for export] *)
Ltac addr_fix H :=
  rewrite ?v_add_ZZ, ?v_add_Zr, ?v_add_Zl, ?v_addi_Z; u_norm;
  lazymatch goal with |- rdn _ _ ?a _ = _ =>
    lazymatch type of H with rdn _ _ ?c _ = _ =>
      first [ constr_eq a c | replace a with c by (f_equal; lia) ] end end;
  exact H.
Ltac ldb F D Hb :=
  chain_step;
  [ reflexivity
  | eapply step_lbu; [ exact F | reflexivity | exact D | gres; imm_norm; rwH; addr_fix Hb ]
  | step_simpl; vnorm ].
Ltac ldbs F D Hb :=
  chain_step;
  [ reflexivity
  | eapply step_lb; [ exact F | reflexivity | exact D | gres; imm_norm; rwH; addr_fix Hb ]
  | step_simpl; vnorm; rewrite ?v_lb_sbyte ].

(* [comment removed for export] *)
Ltac valZ :=
  rewrite ?v_add_ZZ, ?v_add_Zr, ?v_add_Zl, ?v_addi_Z; u_norm;
  try rewrite v_addiw_Z by lia; try rewrite v_subw_ZZ by lia; try rewrite v_addw_ZZ by lia;
  first [ reflexivity | f_equal; lia ].
Ltac pin c tac :=
  lazymatch goal with
  | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
      replace v with (Z_to_bv 64 c : word) by (rwH; symmetry; tac)
  end.
Ltac pinZ c := pin c ltac:(valZ).
Ltac pin_sltu0 := pin 0%Z ltac:(rewrite v_sltu_val; first [rewrite ltu_Zw by lia | rewrite ltu_ZZ by lia]; decide_cmp; reflexivity).
Ltac pin_slti0 := pin 0%Z ltac:(rewrite v_slti_val, signed_Z by lia; decide_cmp; reflexivity).
(* [comment removed for export] *)
Ltac pin_srli3 a := pin (a / 8)%Z ltac:(rewrite v_srli3 by lia; reflexivity).
Ltac pin_andi7 a := pin (a mod 8)%Z ltac:(rewrite v_andi7 by lia; reflexivity).

(* [comment removed for export] *)
Ltac hreg := gres; rwH; first [ reflexivity | assumption | valZ ].
