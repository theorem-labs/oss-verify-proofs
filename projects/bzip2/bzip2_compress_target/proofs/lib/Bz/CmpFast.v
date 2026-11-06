(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import Zify PreOmega.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Arr Cells.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCStream.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sas_g_u32s := repeat lazymatch goal with |- context [length (u32s _)] => rewrite u32s_length end.
Ltac sas_g_u64s := repeat lazymatch goal with |- context [length (u64s _)] => rewrite u64s_length end.
Ltac sas_g_upd := repeat lazymatch goal with |- context [length (upd _ _ _)] => rewrite upd_length end.
Ltac sas_g_zb8 := repeat lazymatch goal with |- context [length (zb8 _ _)] => rewrite zb8_length_nat end.
Ltac sas_g_zw32 := repeat lazymatch goal with |- context [length (zw32 _ _)] => rewrite zw32_length_nat end.
Ltac sas_g_ovb := repeat lazymatch goal with |- context [length (ovb _ _ _)] => rewrite ovb_length_nat end.
Ltac sas_g_ovw := repeat lazymatch goal with |- context [length (ovw _ _ _)] => rewrite ovw_length_nat end.
Ltac sas_g_repeat := repeat lazymatch goal with |- context [length (repeat _ _)] => rewrite repeat_length end.
Ltac sas_g_firstn := repeat lazymatch goal with |- context [length (firstn _ _)] => rewrite length_firstn end.
Ltac sas_g_skipn := repeat lazymatch goal with |- context [length (skipn _ _)] => rewrite length_skipn end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sas_a_u32s := repeat match goal with
  | |- context [length (u32s _)] => rewrite u32s_length
  | H : context [length (u32s _)] |- _ => rewrite u32s_length in H
  end.
Ltac sas_a_u64s := repeat match goal with
  | |- context [length (u64s _)] => rewrite u64s_length
  | H : context [length (u64s _)] |- _ => rewrite u64s_length in H
  end.
Ltac sas_a_upd := repeat match goal with
  | |- context [length (upd _ _ _)] => rewrite upd_length
  | H : context [length (upd _ _ _)] |- _ => rewrite upd_length in H
  end.
Ltac sas_a_zb8 := repeat match goal with
  | |- context [length (zb8 _ _)] => rewrite zb8_length_nat
  | H : context [length (zb8 _ _)] |- _ => rewrite zb8_length_nat in H
  end.
Ltac sas_a_zw32 := repeat match goal with
  | |- context [length (zw32 _ _)] => rewrite zw32_length_nat
  | H : context [length (zw32 _ _)] |- _ => rewrite zw32_length_nat in H
  end.
Ltac sas_a_ovb := repeat match goal with
  | |- context [length (ovb _ _ _)] => rewrite ovb_length_nat
  | H : context [length (ovb _ _ _)] |- _ => rewrite ovb_length_nat in H
  end.
Ltac sas_a_ovw := repeat match goal with
  | |- context [length (ovw _ _ _)] => rewrite ovw_length_nat
  | H : context [length (ovw _ _ _)] |- _ => rewrite ovw_length_nat in H
  end.
Ltac sas_a_repeat := repeat match goal with
  | |- context [length (repeat _ _)] => rewrite repeat_length
  | H : context [length (repeat _ _)] |- _ => rewrite repeat_length in H
  end.
Ltac sas_a_firstn := repeat match goal with
  | |- context [length (firstn _ _)] => rewrite length_firstn
  | H : context [length (firstn _ _)] |- _ => rewrite length_firstn in H
  end.
Ltac sas_a_skipn := repeat match goal with
  | |- context [length (skipn _ _)] => rewrite length_skipn
  | H : context [length (skipn _ _)] |- _ => rewrite length_skipn in H
  end.

(* [comment removed for export] *)
Ltac sas7 := sas_g_u32s; sas_g_u64s; sas_g_upd; sas_g_zb8; sas_g_zw32; sas_g_ovb; sas_g_ovw.
Ltac sas8 := sas7; sas_g_repeat.
Ltac sas10 := sas8; sas_g_firstn; sas_g_skipn.
(* [comment removed for export] *)
Ltac sas7_all := sas_a_u32s; sas_a_u64s; sas_a_upd; sas_a_zb8; sas_a_zw32; sas_a_ovb; sas_a_ovw.
Ltac sas8_all := sas7_all; sas_a_repeat.
Ltac sas10_all := sas8_all; sas_a_firstn; sas_a_skipn.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac eq_lia_guarded :=
  lazymatch goal with
  | |- @eq ?T _ _ =>
      lazymatch T with
      | list _ => fail | option _ => fail | prod _ _ => fail | bool => fail
      | bv _ => fail | cell => fail
      | BzArr.zarr => fail | BzArr.ptrie => fail          (* [comment removed for export] *)
      | _ => lia
      end
  | |- _ => lia
  end.
Ltac rlf := repeat first [ reflexivity | eq_lia_guarded | progress f_equal ].
Ltac rlf_sp := rlf.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bsW_numZ_needw : forall b n v, bw_numZ (bsW b n v) = bw_numZ (bs_needw BS_FUEL b).
Proof. intros b n v. reflexivity. Qed.
Lemma bsW_zb_needw : forall b n v, bw_zb (bsW b n v) = bw_zb (bs_needw BS_FUEL b).
Proof. intros b n v. reflexivity. Qed.
Ltac bsw_same :=
  first [ exact (bsW_numZ_needw _ _ _) | exact (bsW_zb_needw _ _ _)
        | unfold bsPutUInt32; cbv zeta; first [ exact (bsW_numZ_needw _ _ _) | exact (bsW_zb_needw _ _ _) ]
        | reflexivity ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tauto_g := first [ solve [ repeat split; reflexivity ] | tauto ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dm_arith T :=
  lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Peano.le _ _ => idtac | Peano.lt _ _ => idtac
  | _ /\ _ => idtac | _ \/ _ => idtac | ~ _ => idtac | _ <-> _ => idtac
  | ?A -> ?B => lazymatch type of A with Prop => idtac end
  end.
Ltac dm_gen x y :=
  pose proof (Z.div_mod x y); pose proof (Z.mod_pos_bound x y); pose proof (Z.mod_neg_bound x y);
  pose proof (Z.div_0_r_ext x y); pose proof (Z.mod_0_r_ext x y);
  let q := fresh "q" in let r := fresh "r" in
  pose (q := Z.div x y); pose (r := Z.modulo x y);
  repeat match goal with
         | H : context [Z.div x y] |- _ => progress change (Z.div x y) with q in H
         | H : context [Z.modulo x y] |- _ => progress change (Z.modulo x y) with r in H
         end;
  try change (Z.div x y) with q; try change (Z.modulo x y) with r;
  clearbody q r.
Ltac dm_step :=
  match goal with
  | |- context [Z.div ?x ?y] => dm_gen x y
  | |- context [Z.modulo ?x ?y] => dm_gen x y
  | H : ?T |- _ =>
      dm_arith T;
      lazymatch T with
      | context [Z.div ?x ?y] => dm_gen x y; lazymatch type of H with context [Z.div x y] => fail 100 "dm_step: occurrence not replaced" | _ => idtac end
      | context [Z.modulo ?x ?y] => dm_gen x y; lazymatch type of H with context [Z.modulo x y] => fail 100 "dm_step: occurrence not replaced" | _ => idtac end
      end
  end.
Ltac dm2e := repeat dm_step; Z.euclidean_division_equations_cleanup.
(* [comment removed for export] *)
Ltac mlia_lia := lia.
Ltac mlia_fast := dm2e; mlia_lia.

Goal forall a b : Z, (0 < b -> 0 <= a -> a mod b < b /\ a / b * b <= a)%Z.
Proof. intros. mlia_fast. Qed.
Goal forall a : Z, (0 <= a < 2^64 -> (a mod 4294967296) / 65536 < 65536)%Z.
Proof. intros. mlia_fast. Qed.
