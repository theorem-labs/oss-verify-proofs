(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt B_musl_memset_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Section WithMemset.
  Hypothesis memset_spec : memset_stmt.

  Ltac prep :=
    intros until old; intros ARR LEN AL PRG PRT SEP RA;
    pose proof (u8arr_bound _ _ _ _ ARR) as Bd;
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m _) =>
      let a0 := eval vm_compute in (reg_get R 10) in
      let a1 := eval vm_compute in (reg_get R 11) in
      pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m) as MU;
      pose proof (wmono_refl BSEGS m) as WM;
      pose proof (bv_unsigned_in_range 64 a0) as Ra0; unfold bv_modulus in Ra0;
      pose proof (bv_unsigned_in_range 64 a1) as Ra1; unfold bv_modulus in Ra1
    end.

  Ltac tailcall :=
    call memset_spec;
    [ lazymatch goal with H : u8arr _ _ _ _ |- _ => exact H end
    | lazymatch goal with H : Z.of_nat _ = _ |- _ => exact H end
    | lazymatch goal with H : (_ mod 8 = 0)%Z |- _ => exact H end
    | ];
    unfold set_shadow_post; finish;
    match goal with
    | H : u8arr BSEGS _ _ (repeat (fillb ?c) _) |- u8arr BSEGS _ _ _ =>
        let v := eval vm_compute in (fillb c) in change (fillb c) with v in H; exact H
    end.

  #[using="memset_spec"] Lemma set_shadow_00_spec : set_shadow_00_stmt.
  Proof. LiaFast.lf_pins (fun (memset_spec : LiaFast.U) => LiaFast.u0).
    unfold set_shadow_00_stmt, set_shadow_stmt. prep.
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    tailcall.
  Qed.

  #[using="memset_spec"] Lemma set_shadow_f5_spec : set_shadow_f5_stmt.
  Proof. LiaFast.lf_pins (fun (memset_spec : LiaFast.U) => LiaFast.u0).
    unfold set_shadow_f5_stmt, set_shadow_stmt. prep.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    tailcall.
  Qed.
End WithMemset.
