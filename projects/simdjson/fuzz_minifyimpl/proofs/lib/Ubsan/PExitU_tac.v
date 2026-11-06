(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import STRW_tac Startup_kit Amo_tac F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells usegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells usegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac conj_by_addr := repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end); hyp_by_addr.
Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
Ltac nstep := hstep; nlit; try (first [if_true | if_false]).
Ltac xat_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac xsteps_to p := repeat (tryif xat_pc p then fail else nstep).
(* [comment removed for export] *)
Ltac ltu_zero :=
  match goal with |- context [bv_ltu ?x z64] =>
    replace (bv_ltu x z64) with false
      by (symmetry; unfold bv_ltu; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 x) as RX; change (bv_unsigned z64) with 0; clear - RX; lia) end;
  cbn [negb]; cbv iota.

(* [comment removed for export] *)
Lemma lxor_ones_nonneg : forall (x : word), 0 <= Z.lxor (bv_unsigned x) 18446744073709551615.
Proof. intros x. apply Z.lxor_nonneg. pose proof (bv_unsigned_in_range 64 x). split; intros _; lia. Qed.
Ltac bsplit := let K := fresh "K" in if_cases K; zify_cond K;
  try (exfalso; first [ lia | match type of K with context [Z.lxor (bv_unsigned ?x) _] => pose proof (lxor_ones_nonneg x); lia end
                      | match type of K with ?x < 0 => assert (0 <= x) by (apply Z.land_nonneg; right; lia); lia end ]).
Ltac xastep := hstep; try (first [if_true | if_false]).
Ltac run_to p :=
  repeat (tryif xat_pc p then fail
          else first [ (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end; bsplit) | xastep ]).

Lemma bv_eqb_refl_u : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl_u x); cbv iota
  end.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac bstep := hstep; try first [if_lit | if_refl | if_true | if_false].
